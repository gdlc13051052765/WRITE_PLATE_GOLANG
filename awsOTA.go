package main

/*
#include <stdio.h>
#include "awsIotTask.h"
*/
import "C"

import (
	"archive/zip"
	"bufio"
	"fmt"
	"io"
	"log"
	"math"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"strconv"
	"strings"
	"time"
)

// 固件更新进度0--100
var updateOtaProcess int64 = 0

//固件更新文件大小
var otaFileSize int64 = 0

/*=======================================================================================
* 函 数 名： PathExists
* 参    数：
* 功能描述:  查询文件是否存在
* 返 回 值：
* 备    注：
* 作    者： lc
* 创建时间： 2021-06-11
==========================================================================================*/
func PathExists(path string) (bool, error) {
	_, err := os.Stat(path)
	if err == nil {
		return true, nil
	}
	if os.IsNotExist(err) {
		return false, nil
	}
	return false, err
}

/*=======================================================================================
* 函 数 名： Zip
* 参    数：一个是输入源文件, 另一个是输出zip压缩文件
* 功能描述:  压缩文件
* 返 回 值：
* 备    注：
* 作    者： lc
* 创建时间： 2021-06-11
==========================================================================================*/
func Zip(srcFile string, destZip string) error {
	zipfile, err := os.Create(destZip)
	if err != nil {
		return err
	}
	defer zipfile.Close()

	archive := zip.NewWriter(zipfile)
	defer archive.Close()

	filepath.Walk(srcFile, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		header, err := zip.FileInfoHeader(info)
		if err != nil {
			return err
		}

		header.Name = path
		if info.IsDir() {
			header.Name += "/"
		} else {
			header.Method = zip.Deflate
		}

		writer, err := archive.CreateHeader(header)
		if err != nil {
			return err
		}

		if !info.IsDir() {
			file, err := os.Open(path)
			if err != nil {
				return err
			}
			defer file.Close()
			_, err = io.Copy(writer, file)
		}
		return err
	})

	return err
}

/*=======================================================================================
* 函 数 名： Unzip
* 参    数：一个是输入源zip文件, 另一个是输出路径
* 功能描述:  压缩文件
* 返 回 值：
* 备    注：
* 作    者： lc
* 创建时间： 2021-09-24
==========================================================================================*/
func Unzip(zipFile string, destDir string) error {
	zipReader, err := zip.OpenReader(zipFile)
	if err != nil {
		return err
	}
	defer zipReader.Close()

	for _, f := range zipReader.File {
		fpath := filepath.Join(destDir, f.Name)
		if f.FileInfo().IsDir() {
			os.MkdirAll(fpath, os.ModePerm)
		} else {
			if err = os.MkdirAll(filepath.Dir(fpath), os.ModePerm); err != nil {
				return err
			}

			inFile, err := f.Open()
			if err != nil {
				return err
			}
			defer inFile.Close()

			outFile, err := os.OpenFile(fpath, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, f.Mode())
			if err != nil {
				return err
			}
			defer outFile.Close()

			_, err = io.Copy(outFile, inFile)
			if err != nil {
				return err
			}
		}
	}
	return nil
}

/*=======================================================================================
* 函 数 名： 获取ntp连接状态
* 参    数：
* 功能描述:  ntp时间获取成功返回1
* 返 回 值：
* 备    注：
* 作    者： lc
* 创建时间： 2021-06-11
==========================================================================================*/
//export get_net_status
func get_net_status() int {
	if netConnectStatus == true {
		return 1
	} else {
		return 0
	}
}

/*=======================================================================================
* 函 数 名： aws_ota_handler
* 参    数：
* 功能描述:  aws ota 从url 获取固件文件
* 返 回 值：
* 备    注：
* 作    者： lc
* 创建时间： 2021-06-11
==========================================================================================*/
//export aws_ota_handler
func aws_ota_handler(durl *C.char) int {
	urlstr := C.GoString(durl)
	downurl := strings.Replace(urlstr, "https", "http", 5)
	fmt.Printf("固件下载地址 = %s \n", downurl)
	uri, err := url.ParseRequestURI(downurl)
	if err != nil {
		panic("网址错误")
		return -1
	}
	//发送固件开始更新命令到QT
	C.aws_send_ota_update_to_qt(C.int(OTA_START_UPDATE), C.int(updateOtaProcess))
	filename := path.Base(uri.Path)
	log.Println("[*] Filename " + filename)

	client := http.DefaultClient
	client.Timeout = time.Second * 60 //设置超时时间
	resp, err := client.Get(downurl)
	if err != nil {
		panic(err)
		return -1
	}
	//读取服务器返回的文件大小
	fsize, err := strconv.ParseInt(resp.Header.Get("Content-Length"), 10, 32)
	if err != nil {
		fmt.Println(err)
	}
	otaFileSize = fsize
	fmt.Printf("要下载的文件大小 = %d \n", otaFileSize)
	if resp.ContentLength <= 0 {
		log.Println("[*] Destination server does not support breakpoint download.")
	}
	raw := resp.Body
	defer raw.Close()
	reader := bufio.NewReaderSize(raw, 1024*32)

	newFileName := fmt.Sprintf("/home/meican/otafiles/%s", "mctota.zip") //创建新固件文件
	file, err := os.Create(newFileName)
	if err != nil {
		panic(err)
		return -1
	}

	buff := make([]byte, 32*1024)
	written := 0
	go func() {
		for {
			nr, er := reader.Read(buff)
			if nr > 0 {
				nw, ew := io.WriteString(file, string(buff[0:nr]))
				//fmt.Printf("文件读取数据 = %s\n", string(buff[0:nr]))
				if nw > 0 {
					written += nw
				}
				if ew != nil {
					err = ew
					break
				}
				if nr != nw {
					err = io.ErrShortWrite
					break
				}
			}
			if er != nil {
				if er != io.EOF {
					err = er
				}
				break
			}
		}
		if err != nil {
			updateOtaProcess = 100
			C.aws_send_ota_update_to_qt(C.int(OTA_UPDATE_FAIL), C.int(updateOtaProcess))
			panic(err)
			return
		}
	}()

	spaceTime := time.Second * 1
	ticker := time.NewTicker(spaceTime)
	lastWtn := 0
	stop := false

	for {
		select {
		case <-ticker.C:
			speed := written - lastWtn
			fmt.Printf("Speed %s / %s \n", bytesToSize(speed), spaceTime.String())
			fmt.Printf("已下载文件进度 = %d \n", written)
			//发送固件更新进度到QT
			updateOtaProcess = (int64(written) * 100) / otaFileSize
			fmt.Printf("已下载文件进度条 = %d \n", updateOtaProcess)
			C.aws_send_ota_update_to_qt(C.int(OTA_UPDATE_PROCESS), C.int(updateOtaProcess))
			if written-lastWtn == 0 {
				ticker.Stop()
				stop = true
				fmt.Printf("文件下载完成 \n")
				file.Close()

				cmd := exec.Command("/bin/sh", "-c", "rm -rf /home/meican/ota")
				if err := cmd.Start(); err != nil { // 运行命令
					fmt.Println(err)
				}
				if err := cmd.Wait(); err != nil {
					fmt.Println("wait1:", err.Error())
				}
				for {
					if res, err := PathExists("/home/meican/otafiles/mctota.zip"); err != nil { // 运行命令
						fmt.Println(err)
					} else {
						if res == true {
							// cmd = exec.Command("/bin/sh", "-c", "unzip /home/meican/otafiles/mctota.zip")
							// if err := cmd.Start(); err != nil { // 运行命令
							// 	fmt.Println(err)
							// }
							// if err := cmd.Wait(); err != nil {
							// 	fmt.Println("wait2:", err.Error())
							// }

							if err := Unzip("/home/meican/otafiles/mctota.zip", "/home/meican"); err == nil {
								cmd = exec.Command("/bin/sh", "-c", "chmod 777 /home/meican/ota/run.sh")
								if err := cmd.Start(); err != nil { // 运行命令
									fmt.Println(err)
								}
								if err := cmd.Wait(); err != nil {
									fmt.Println("wait3:", err.Error())
								}
							}
							break
						}
					}
					//time.Sleep(1 * time.Second)
				}

				return 0
				//break
			}
			lastWtn = written
		}
		if stop {
			break
		}
	}
	return -1
}

func bytesToSize(length int) string {
	var k = 1024 // or 1024
	var sizes = []string{"Bytes", "KB", "MB", "GB", "TB"}
	if length == 0 {
		return "0 Bytes"
	}
	i := math.Floor(math.Log(float64(length)) / math.Log(float64(k)))
	r := float64(length) / math.Pow(float64(k), i)
	return strconv.FormatFloat(r, 'f', 3, 64) + " " + sizes[int(i)]
}

/*=======================================================================================
* 函 数 名： reboot_qt_app
* 参    数：
* 功能描述:  重启qt程序
* 返 回 值：
* 备    注：
* 作    者： lc
* 创建时间： 2021-06-11
==========================================================================================*/
//export reboot_qt_app
func reboot_qt_app() {
	cmd := exec.Command("/bin/sh", "-c", "kill -9 $(pidof WriteDisk)")
	if err := cmd.Start(); err != nil { // 运行命令
		fmt.Println(err)
	}
	if err := cmd.Wait(); err != nil {
		fmt.Println("wait1:", err.Error())
	}

	cmd = exec.Command("/bin/sh", "-c", "/home/meican/WriteDisk")
	if err := cmd.Start(); err != nil { // 运行命令
		fmt.Println(err)
	}
	if err := cmd.Wait(); err != nil {
		fmt.Println("wait1:", err.Error())
	}
}
