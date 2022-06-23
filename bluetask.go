package main

/*
#include <stdio.h>
#include "rewrCardTask.h"
#include "sqliteTask.h"
#include "msgTask.h"
#include "cAppTask.h"
#include "awsIotTask.h"
*/
import "C"

import (
	"bufio"
	"bytes"
	"encoding/base64"
	"fmt"
	"io"
	"os"
	"os/exec"
	"strconv"
	"strings"
)

//wifi配置状态机
const (
	GET_SSID_PASSWORD = 0 //获取到SSID账号密码
)

/*==================================================================================
* 函 数 名： blue_scan_dev
* 参    数： None
* 功能描述:  命令行搜索蓝牙设备
* 返 回 值： None
* 备    注： None
* 作    者： lc
* 创建时间： 2021/7/11
==================================================================================*/
func write_data_wifi_config_file(ssid string, psk string) error {
	//读写方式打开文件
	file, err := os.OpenFile("/etc/wpa_supplicant.conf", os.O_RDWR, 0666)
	if err != nil {
		fmt.Println("open file filed.", err)
		return err
	}
	//defer关闭文件
	defer file.Close()

	//获取文件大小
	stat, err := file.Stat()
	if err != nil {
		panic(err)
	}
	var size = stat.Size()
	fmt.Println("file size:", size)

	var content string //存储新的文件内容
	//读取文件内容到io中
	reader := bufio.NewReader(file)
	pos := int64(0)
	for {
		//读取每一行内容
		line, err := reader.ReadString('\n')
		if err != nil {
			//读到末尾
			if err == io.EOF {
				fmt.Println("File read ok!")
				break
			} else {
				fmt.Println("Read file error!", err)
				return err
			}
		}
		fmt.Println(line)

		//根据关键词覆盖当前行
		if strings.Contains(line, "ssid") {
			bytes := []byte("        ssid=" + "\"" + ssid + "\"" + "\n")
			content += string(bytes)
			//file.WriteAt(bytes, pos)
		} else if strings.Contains(line, "psk") {
			//strings.Replace(psk, "\n", "", -1)
			bytes := []byte("        psk=" + "\"" + psk + "\"" + "\n")
			content += string(bytes)
			content += "}"
			fmt.Printf("write psk = %s\n", content)
			break
			//file.WriteAt(bytes, pos)
		} else {
			content += line
		}

		//每一行读取完后记录位置
		pos += int64(len(line))
	}
	err = file.Truncate(0) //清空文件
	if nil != err {
		return err
	}

	_, err = file.Seek(0, 0) //将文件指针指向文件起始位置，保证从头写入文件
	if nil != err {
		return err
	}

	_, err = file.WriteString(content) //向文件写入新的内容
	if nil != err {
		return err
	}
	return nil
}

/*==================================================================================
* 函 数 名： blue_scan_dev
* 参    数： None
* 功能描述:  命令行搜索蓝牙设备
* 返 回 值： None
* 备    注： None
* 作    者： lc
* 创建时间： 2021/7/11
==================================================================================*/
var ssidtempbuffer bytes.Buffer //ssid缓存
var ssidrecnum uint8 = 1

var pdtempbuffer bytes.Buffer //passward 密码缓存
var pdrecnum uint8 = 1

var sdtempbuffer bytes.Buffer //餐厅ID缓存
var sdrecnum uint8 = 1

var tktempbuffer bytes.Buffer //token缓存
var tkrecnum uint8 = 1

var blueScanStatus int = -1 //接收蓝牙广播数据状态机

//var stdout io.ReadCloser
var setBlueScan bool = false //开始搜索蓝牙开机只开启一次

func blue_scan_dev() int {
	var ssidstr string
	var pskstr string
	var bWifiConSta = [5]bool{false, false, false, false, false}
	blueScanStatus = -1

	key := []byte("rlnqflkewnlfwnjf") // AES加密的密钥,跟写盘器助手保持一致

Loop:
	fmt.Println("配置蓝牙网络")
	cmd := exec.Command("/bin/sh", "-c", "hcitool lescan")
	stdout, _ := cmd.StdoutPipe()
	defer stdout.Close()                // 保证关闭输出流
	if err := cmd.Start(); err != nil { // 运行命令
		fmt.Println(err)
	}

	//使用带缓冲的读取器
	outputBuf := bufio.NewReader(stdout)
	outputBuf.Reset(stdout)
	for {
		//fmt.Println("蓝牙搜索")
		//一次获取一行,_ 获取当前行是否被读完
		output, _, err := outputBuf.ReadLine()
		if err != nil {
			// 判断是否到文件的结尾了否则出错
			if err.Error() != "EOF" {
				debug_printf("Error eof :%s\n", err)
			}
		}
		if err := strings.Index(string(output), "unknown"); err != -1 {
			//debug_printf("unknown = %s\n", string(output))
		} else {
			if string(output) == "" {
				outputBuf.Reset(stdout)
				fmt.Println("蓝牙搜索数据为空")
				cmd = exec.Command("/bin/sh", "-c", "/home/meican/setblue.sh")
				if err := cmd.Start(); err != nil { // 运行命令
					fmt.Println(err)
				}
				goto Loop
			}
			debug_printf("out = %s \n", string(output))
		}

		//配置wifi 账号 SSID
		if err := strings.Index(string(output), "si"); err != -1 {
			debug_printf("si = %s\n", string(output))
			if bWifiConSta[0] == false {
				//debug_printf("si = %s\n", string(output))
				//debug_printf("si = %v\n", output)
				if len(output) < err+4 { //数据长度不足
					return blueScanStatus
				}

				toalindex := output[err+2 : err+3] //截取总包号
				debug_printf("toalindex = %d\n", toalindex[0])

				index := output[err+3 : err+4] //截取当前标号
				debug_printf("index = %d\n", index[0])
				if index[0] == ssidrecnum {
					ssidtempbuffer.Write(output[err+4:])
					ssidrecnum++
					debug_printf("ssidbuffer = %s ssidrecnum = %d\n", ssidtempbuffer.String(), ssidrecnum)
				}
				if toalindex[0]+1 == ssidrecnum {
					debug_printf("ssidbuffer = %s\n", ssidtempbuffer.String())
					ssidrecnum = 1
					decoded, _ := base64.StdEncoding.DecodeString(ssidtempbuffer.String()) //base64解密
					debug_printf("SSID base64 解密结果 = %s\n", string(decoded))
					decrypted, err := AESDecrypt(decoded, key) //AES解密
					if err != nil {
						ssidtempbuffer.Reset() //清空                           //解密失败
						return -1
					}
					debug_printf("SSID AES 解密结果 = %s\n", string(decrypted))
					ssidstr = string(decrypted)
					ssidtempbuffer.Reset() //清空
					bWifiConSta[0] = true  //获取到wifi账号
				}
			}
		}
		//配置wifi密码 PASSWORD
		if err := strings.Index(string(output), "pd"); err != -1 {
			debug_printf("pd = %s\n", string(output))
			if bWifiConSta[1] == false {
				debug_printf("pd = %v\n", output)
				toalindex := output[err+2 : err+3] //截取总包号
				debug_printf("toalindex = %d\n", toalindex[0])

				index := output[err+3 : err+4] //截取当前标号
				debug_printf("index = %d\n", index[0])
				if index[0] == pdrecnum {
					pdtempbuffer.Write(output[err+4:])
					pdrecnum++
					debug_printf("pdbuffer = %s pdrecnum = %d\n", pdtempbuffer.String(), pdrecnum)
				}
				if toalindex[0]+1 == pdrecnum {
					debug_printf("pdbuffer = %s\n", pdtempbuffer.String())
					pdrecnum = 1
					decoded, _ := base64.StdEncoding.DecodeString(pdtempbuffer.String()) //base64 解密
					debug_printf("PASSWORD BASE64 解密结果 = %s\n", string(decoded))
					decrypted, err := AESDecrypt(decoded, key) //AES解密
					if err != nil {                            //解密失败
						pdtempbuffer.Reset() //清空
						return -1
					}
					debug_printf("PASSWORD AES 解密结果 = %s\n", string(decrypted))
					pskstr = string(decrypted)
					pdtempbuffer.Reset()  //清空
					bWifiConSta[1] = true //获取到wifi 密码
				}
			}
		}
		//配置餐厅id
		if err := strings.Index(string(output), "sd"); err != -1 {
			debug_printf("sd = %s\n", string(output))
			if bWifiConSta[2] == false {
				debug_printf("sd = %v\n", output)
				toalindex := output[err+2 : err+3] //截取总包号
				debug_printf("toalindex = %d\n", toalindex[0])

				index := output[err+3 : err+4] //截取当前标号
				debug_printf("index = %d\n", index[0])
				if index[0] == sdrecnum {
					sdtempbuffer.Write(output[err+4:])
					sdrecnum++
					debug_printf("pdbuffer = %s pdrecnum = %d\n", sdtempbuffer.String(), sdrecnum)
				}
				if toalindex[0]+1 == sdrecnum {
					debug_printf("pdbuffer = %s\n", sdtempbuffer.String())
					sdrecnum = 1
					decoded, _ := base64.StdEncoding.DecodeString(sdtempbuffer.String()) //base64 解密
					debug_printf("SD BASE64 解密结果 = %s\n", string(decoded))
					decrypted, err := AESDecrypt(decoded, key) //AES解密
					if err != nil {                            //解密失败
						sdtempbuffer.Reset() //清空
						return -1
					}
					debug_printf("SD AES 解密结果 = %s\n", string(decrypted))
					//deviceMsg.RestaurantID, _ = strconv.Atoi(string(decrypted))
					bindRestaurantID, _ = strconv.Atoi(string(decrypted))
					debug_printf("餐厅ID = %d\n", bindRestaurantID)
					sdtempbuffer.Reset() //清空
					bWifiConSta[2] = true
				}
			}
		}
		//配置现场绑定token
		if err := strings.Index(string(output), "tk"); err != -1 {
			debug_printf("tk = %s\n", string(output))
			if bWifiConSta[3] == false {
				debug_printf("tk = %v\n", output)
				toalindex := output[err+2 : err+3] //截取总包号
				debug_printf("toalindex = %d\n", toalindex[0])

				index := output[err+3 : err+4] //截取当前标号
				debug_printf("index = %d\n", index[0])
				if index[0] == tkrecnum {
					tktempbuffer.Write(output[err+4:])
					tkrecnum++
					debug_printf("tkbuffer = %s tkrecnum = %d\n", tktempbuffer.String(), tkrecnum)
				}
				if toalindex[0]+1 == tkrecnum {
					debug_printf("tkbuffer = %s\n", tktempbuffer.String())
					pdrecnum = 1
					decoded, _ := base64.StdEncoding.DecodeString(tktempbuffer.String()) //base64 解密
					debug_printf("token BASE64 解密结果 = %s\n", string(decoded))
					decrypted, err := AESDecrypt(decoded, key) //AES解密
					if err != nil {                            //解密失败
						tktempbuffer.Reset() //清空
						return -1
					}
					debug_printf("token AES 解密结果 = %s\n", string(decrypted))
					siteBindToken = string(decrypted)
					debug_printf("siteBindToken = %s\n", siteBindToken)
					tktempbuffer.Reset() //清空
					bWifiConSta[3] = true
				}
			}
		}
		//fmt.Printf("bWifiConSta[0] = %v; bWifiConSta[1] = %v;bWifiConSta[2] = %v;bWifiConSta[3] = %v\n", bWifiConSta[0], bWifiConSta[1], bWifiConSta[2], bWifiConSta[3])
		if deviceMsg.Status == INIT_STATUS { //工厂绑定只需获取wifi 账号跟密码
			if bWifiConSta[0] == true && bWifiConSta[1] == true {
				write_data_wifi_config_file(ssidstr, pskstr)
				blueScanStatus = 0

				//cmd.Process.Pid
				cmd.Process.Kill()

				cmd := exec.Command("/bin/sh", "-c", "kill -9 $(pidof  hcitool lescan)")
				if err := cmd.Start(); err != nil { // 运行命令
					fmt.Println(err)
				}
				if err := cmd.Wait(); err != nil {
					fmt.Println("wait:", err.Error())
				}

				cmd = exec.Command("/bin/sh", "-c", "kill -9 $(pidof brcm_patchram_plus)")
				if err := cmd.Start(); err != nil { // 运行命令
					fmt.Println(err)
				}
				if err := cmd.Wait(); err != nil {
					fmt.Println("wait:", err.Error())
				}

				cmd = exec.Command("/bin/sh", "-c", "kill -9 $(pidof hcitool)")
				if err := cmd.Start(); err != nil { // 运行命令
					fmt.Println(err)
				}
				if err := cmd.Wait(); err != nil {
					fmt.Println("wait:", err.Error())
				}

				cmd = exec.Command("/bin/sh", "-c", "/home/meican/setblue.sh")
				if err := cmd.Start(); err != nil { // 运行命令
					fmt.Println(err)
				}
				stdout.Close() // 保证关闭输出流
				return blueScanStatus
			}
		} else { //现场绑定获取wifi账号，密码以及餐厅id，token
			if bWifiConSta[0] == true && bWifiConSta[1] == true && bWifiConSta[2] == true && bWifiConSta[3] == true {
				write_data_wifi_config_file(ssidstr, pskstr)
				blueScanStatus = 0

				cmd.Process.Kill()

				cmd := exec.Command("/bin/sh", "-c", "kill -9 $(pidof  hcitool lescan)")
				if err := cmd.Start(); err != nil { // 运行命令
					fmt.Println(err)
				}
				if err := cmd.Wait(); err != nil {
					fmt.Println("wait:", err.Error())
				}

				cmd = exec.Command("/bin/sh", "-c", "kill -9 $(pidof brcm_patchram_plus)")
				if err := cmd.Start(); err != nil { // 运行命令
					fmt.Println(err)
				}
				if err := cmd.Wait(); err != nil {
					fmt.Println("wait:", err.Error())
				}

				cmd = exec.Command("/bin/sh", "-c", "/home/meican/setblue.sh")
				if err := cmd.Start(); err != nil { // 运行命令
					fmt.Println(err)
				}
				stdout.Close() // 保证关闭输出流
				return blueScanStatus
			}
		}
	}
	// if err := cmd.Wait(); err != nil {
	// 	fmt.Println("wait:", err.Error())
	// }
	return blueScanStatus
}
