package main

/*
#include <stdio.h>
#include "rewrCardTask.h"
#include "sqliteTask.h"
#include "msgTask.h"
#include "cAppTask.h"
#include "awsIotTask.h"
#include "crc.h"
#include "readTxt.h"
#include "beepMotor.h"
#cgo CFLAGS: -I./
#cgo LDFLAGS: -L./ -lsqlite3 -lrfal_st25r3916 -lst25_api -lwificonfig -lAwsIotSdk -lmbedtls -lmbedcrypto -lmbedx509 -lm
*/
import "C"
import (
	"bufio"
	"fmt"
	"log"
	"os"
	"os/exec"
	"time"
)

/*==================================================================================
                      全局变量
==================================================================================*/

//ip地址信息结构体
var posipstr _IpMessage

//设备地址信息
var posDevstr _DevMsgCon

//写盘器软件版本
//写盘器启动失败备份程序编译
// var backUpAppFlag bool = true       //true 编译备份程序
// var version string = "backup.0.0.0" // 备份程序版本

var backUpAppFlag bool = false //true 编译备份程序
// var version string = "writeTest.0.0.23"
// thomas yang begin
var version string = "MCT_DM2_0.0.16"

// thomas yang end
//var version string = "TestTest.0.0.1"

//开始配置网络标记
var wPSetWifiFlag int = 0

//联网成功标记
var netConnectStatus bool = false //false == 联网失败；true == 联网成功

/*==================================================================================
* 函 数 名： write_plate_app_init
* 参    数：
* 功能描述:  设备初始化函数
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/4/14
==================================================================================*/
func write_plate_app_init() {
	//读取ip地址信息
	posipstr = read_ip_from_txt()
	debug_printf("posipstr.ip = %v\n", posipstr.localip)
	debug_printf("posipstr.mask = %v\n", posipstr.mask)
	debug_printf("posipstr.gateway = %v\n", posipstr.gateway)
	debug_printf("posipstr.routeip = %v\n", posipstr.routeip)
	debug_printf("posipstr.port = %v\n", posipstr.port)
	debug_printf("posipstr.stationcode = %v\n", posipstr.stationcode)
	debug_printf("posipstr.maincode = %v\n", posipstr.maincode)
	debug_printf("posipstr.nonet = %v\n", posipstr.nonet)

	//http 参数配置初始化
	http_client_parameter_init(posipstr, posDevstr)
	//写盘读写器初始化
	C.nfc_read_card_init()
	//创建主菜单数据库
	mainSqliteDb := C.CString("menu_lev1")
	C.sqlite_create_menu_db(mainSqliteDb)
	//创建写盘信息数据库
	//C.sqlite_create_food_menu_db()
	//创建配置数据库
	//C.sqlite_create_config_db()
	//创建进程保护数据库
	//C.sqlite_create_process_protection_db()
	//写入进程运行数据库运行标记位
	if backUpAppFlag == false {
		C.sqlite_update_process_protection_db()
	}
	//创建qt进程通讯消息队列
	C.create_qt_msg()
	//创建C多任务
	C.app_wrplate_create_thread()
	//从配置数据库读取配置信息
	write_plate_read_msg_from_config_sqlite()
	//C蜂鸣器初始化
	C.beep_motor_init()
}

/*==================================================================================
* 函 数 名： write_plate_init_ntp_time
* 参    数：
* 功能描述:  初始化 ntp 时间
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/29
==================================================================================*/
var ntpflag bool = true
var ntpWifiCheckFlag = false

func write_plate_init_ntp_time() {
	for {
		if ntpflag == true {
			if err := ntp_time_calibration(); err == nil {
				debug_printf("NTP 时间设置成功 \n")
				netConnectStatus = true //联网成功
				if wPSetWifiFlag == 1 { //接收到配网指令，联网后回复QT联网成功指令
					netstatus := 0
					C.msg_send_net_connect_status(C.int(netstatus))
					wPSetWifiFlag = 0
					if ntpWifiCheckFlag == false {
						cmd := exec.Command("/bin/sh", "-c", "/home/meican/rebootgolang.sh")
						if err := cmd.Start(); err != nil { // 运行命令
							fmt.Println(err)
						}
						if err := cmd.Wait(); err != nil {
							fmt.Println("wait:", err.Error())
						}
					}
				}
				ntpflag = false
				currentTime := time.Now()
				fmt.Println("wifi配置结束时间 = ", currentTime)
			} else {
				netConnectStatus = false //联网失败
				// netstatus := 1
				// C.msg_send_net_connect_status(C.int(netstatus))
				debug_printf("NTP 时间设置失败 \n")
			}
		}
		time.Sleep(3 * time.Second)
	}
}

/*==================================================================================
* 函 数 名： write_plate_blue_scan
* 参    数：
* 功能描述:  广播扫描蓝牙名字，从名字中解析WiFi配置参数；现场绑定密钥
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/29
==================================================================================*/
var blueflag bool = false    //是否开始接收蓝牙广播标记 false 开始接收
var mainTaskFlag bool = true //主任务运行标志位，true==运行，

func write_plate_blue_scan() {
	for {
		if blueflag == true {
			mainTaskFlag = false //停止其他任务
			ntpflag = false      //停止获取ntp时间
			currentTime := time.Now()
			fmt.Println(currentTime)

			status := blue_scan_dev()
			if status == 0 {
				blueflag = false //蓝牙广播设置成功停止接收广播
				time.Sleep(1 * time.Second)
				debug_printf("蓝牙广播设置成功 \n")
				currentTime := time.Now()
				fmt.Println(currentTime)
				cmd := exec.Command("/bin/sh", "-c", "ifconfig wlan0 down")
				if err := cmd.Start(); err != nil { // 运行命令
					fmt.Println(err)
				}
				if err := cmd.Wait(); err != nil {
					fmt.Println("wait:", err.Error())
				}

				cmd = exec.Command("/bin/sh", "-c", "kill -9 $(pidof wpa_supplicant)")
				if err := cmd.Start(); err != nil { // 运行命令
					fmt.Println(err)
				}
				if err := cmd.Wait(); err != nil {
					fmt.Println("wait:", err.Error())
				}

				cmd = exec.Command("/bin/sh", "-c", "/opt/mc_shell/wifi_connect.sh")
				//cmd = exec.Command("/bin/sh", "-c", "/home/mc_shell/wifi_connect.sh")
				if err := cmd.Start(); err != nil { // 运行命令
					fmt.Println(err)
				}
				if err := cmd.Wait(); err != nil {
					fmt.Println("wait:", err.Error())
				}
				ntpflag = true                    //网络重新配置后需重新获取ntp时间
				mainTaskFlag = true               //恢复主任务
				C.resume_aws_iot_monitor_thread() //恢复AWS IOT 线程
			}
		}
		time.Sleep(10 * time.Millisecond)
	}
}

/*==================================================================================
* 函 数 名： write_plate_timed_task
* 参    数：
* 功能描述:  写盘器定时任务
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/29
==================================================================================*/
func write_plate_timed_task() {
	//定时任务
	ticker := time.NewTicker(time.Second * 20) //10分钟
	for range ticker.C {
		fmt.Println(time.Now().Format("2006-01-02 15:04:05"))
		C.write_plate_aws_iot_poll_jobs_next()
		time.Sleep(1 * time.Second)
	}
}

/*==================================================================================
* 函 数 名： write_plate_write_cpu_log_task
* 参    数：
* 功能描述:  写盘器定时写cpu温度跟频率log
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/29
==================================================================================*/
func write_plate_write_cpu_log_task() {
	var file *os.File
	var err error

	for {
		//以年月日为后缀创建CPU温度频率log文件
		year := time.Now().Format("2006")
		month := time.Now().Format("01")
		day := time.Now().Format("02")
		filename := fmt.Sprintf("/home/meican/logfiles/temp-%s-%s-%s.log", year, month, day)
		if checkFileIsExist(filename) { //如果文件存在
			file, err = os.OpenFile(filename, os.O_RDWR|os.O_APPEND, 0666) //打开文件不清空已追加方式打开，写入文件末尾
			fmt.Println("温度log文件存在")
		} else {
			file, err = os.Create(filename) //创建文件
			fmt.Println("温度log文件不存在")
		}

		logger := log.New(file, "", log.Llongfile)
		logger.Println("2.Println log with log.LstdFlags ...")
		//默认会有log.Ldate | log.Ltime（日期 时间），这里重写为 日 时 文件名
		//log.SetFlags(log.Ldate | log.Ltime | log.Lshortfile) //2015/04/22 11:28:41 test.go:29: content
		log.SetFlags(log.Ldate | log.Ltime) //2015/04/22 11:28:41  content

		//获取温度
		cmd := exec.Command("/bin/sh", "-c", "cat /sys/devices/virtual/thermal/thermal_zone0/temp")
		stdout, _ := cmd.StdoutPipe()
		//defer stdout.Close()                // 保证关闭输出流
		if err := cmd.Start(); err != nil { // 运行命令
			fmt.Println(err)
		}
		//使用带缓冲的读取器
		outputBuf := bufio.NewReader(stdout)
		//一次获取一行,_ 获取当前行是否被读完
		output, _, err1 := outputBuf.ReadLine()
		if err1 != nil {
			// 判断是否到文件的结尾了否则出错
			if err1.Error() != "EOF" {
				debug_printf("Error :%s\n", err1)
			}
		}
		if err1 := cmd.Wait(); err1 != nil {
			fmt.Println("wait:", err1.Error())
		}
		// debug_printf("out = %v \n", output)
		// debug_printf("temperature = %s \n", string(output))
		temperature := string(output) //获取CPU温度

		//获取CPU频率
		cmd = exec.Command("/bin/sh", "-c", "cat /sys/devices/system/cpu/cpu0/cpufreq/cpuinfo_cur_freq")
		stdout, _ = cmd.StdoutPipe()
		//	defer stdout.Close()                // 保证关闭输出流
		if err := cmd.Start(); err != nil { // 运行命令
			fmt.Println(err)
		}
		//使用带缓冲的读取器
		outputBuf = bufio.NewReader(stdout)
		//一次获取一行,_ 获取当前行是否被读完
		output, _, err = outputBuf.ReadLine()
		if err != nil {
			// 判断是否到文件的结尾了否则出错
			if err.Error() != "EOF" {
				debug_printf("Error :%s\n", err)
			}
		}
		if err := cmd.Wait(); err != nil {
			fmt.Println("wait:", err.Error())
		}
		// debug_printf("out = %v \n", output)
		// debug_printf("frequency = %s \n", string(output))
		frequency := string(output) //获取CPU频率

		//write log
		log.SetOutput(file)
		log.Printf("CPU温度 = %v, CPU主频 = %v \n", temperature, frequency)
		file.Close()
		time.Sleep(5 * time.Second)
	}
}

//主流程
func main() {
	fmt.Printf("MCT写盘器软件版本 == %s\n", version)
	//初始化
	write_plate_app_init()

	//获取ntp时间
	go write_plate_init_ntp_time()
	//蓝牙广播获取 wifi账号跟密码
	go write_plate_blue_scan()
	//写盘器定时任务
	//go write_plate_timed_task()
	//定时写cpu温度跟频率log
	//go write_plate_write_cpu_log_task()

	for {
		//主任务
		if mainTaskFlag == true {
			write_plate_main_task()
		}
		time.Sleep(1 * time.Second)
	}
}
