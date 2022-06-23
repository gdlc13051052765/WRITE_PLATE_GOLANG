/*****************************************************************************************
 * 文件说明：
 * 写盘器不同状态下相应的流程处理
 *
 *****************************************************************************************/

package main

/*
#include <stdio.h>
#include "rewrCardTask.h"
#include "sqliteTask.h"
#include "msgTask.h"
#include "cAppTask.h"
#include "awsIotTask.h"
#cgo CFLAGS: -I./
#cgo LDFLAGS: -L./ -lsqlite3 -lrfal_st25r3916 -lst25_api -lwificonfig -lAwsIotSdk -lmbedtls -lmbedcrypto -lmbedx509 -lm
*/
import "C"
import (
	"fmt"
	"os/exec"
	"time"
)

/*=================================全局变量==========================================*/
//token 接口地址
var tokenUrl string = ""

//设备状态枚举
const (
	INIT_STATUS            = 0 //生产状态
	WAIT_TOPIC_STATUS      = 1 //证书获取完成等待订阅
	FACTORY_BIND_OK_STATUS = 2 //完成出厂绑定（解绑状态）
	SITE_BIND_OK_STATUS    = 3 //现场绑定完成，可以正常写盘拉菜单
	LOCAL_UNBIND_STATUS    = 4 //本地解绑完成，一直上传解绑状态到后台
)

//菜单获取状态枚举
const (
	START_GET_MENU     = 0 //开始获取菜单
	GET_STATUS_OK      = 1 //菜单获取成功
	GET_STATUS_FAIL    = 2 //菜单获取失败
	GET_STATUS_PROCESS = 3 //菜单获取进度
)

//固件更新状态枚举
const (
	OTA_START_UPDATE   = 0 //固件开始更新
	OTA_UPDATE_OK      = 1 //固件更新成功
	OTA_UPDATE_FAIL    = 2 //固件更新失败
	OTA_UPDATE_PROCESS = 3 //固件更新进度
)

/*==================================================================================*/

/*==================================================================================
* 函 数 名： write_plate_init_process
* 参    数：
* 功能描述:  写盘器工厂初始流程
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/09
==================================================================================*/
func write_plate_init_process() {
	write_plate_http_devices_init(tokenUrl) //调用美餐后台设备初始化接口获取AWS平台CA证书 uuid，设备id
}

/*==================================================================================
* 函 数 名： write_plate_site_bind_process
* 参    数：
* 功能描述:  连接AWS IOT 后台
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/09
==================================================================================*/
func write_plate_init_iot_process() {
}

/*==================================================================================
* 函 数 名： write_plate_site_bing_process
* 参    数：
* 功能描述:  写盘器现场绑定
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/09
==================================================================================*/
func write_plate_site_bing_process() {
	write_plate_http_site_bind("")
}

/*==================================================================================
* 函 数 名： write_plate_clear_menu
* 参    数：
* 功能描述:  写盘器解绑后，或者更新菜单前先清空菜单数据库
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/09
==================================================================================*/
func write_plate_clear_menu() {
	//删除包含menu的菜单数据库文件
	//cmd := exec.Command("/bin/sh", "-c", `find -name "/home/meican/menudb/menu*" | xargs rm -rfv`)
	cmd := exec.Command("/bin/sh", "-c", "rm -rf /home/meican/menudb/")
	if err := cmd.Start(); err != nil {
		fmt.Println(err)
	}
	if err := cmd.Wait(); err != nil {
		fmt.Println(err)
	}
	cmd = exec.Command("/bin/sh", "-c", "mkdir /home/meican/menudb")
	if err := cmd.Start(); err != nil {
		fmt.Println(err)
	}
	if err := cmd.Wait(); err != nil {
		fmt.Println(err)
	}
	//创建主菜单数据库
	mainSqliteDb := C.CString("menu_lev1")
	C.sqlite_create_menu_db(mainSqliteDb)
}

/*==================================================================================
* 函 数 名： write_plate_site_work_process
* 参    数：
* 功能描述:  写盘器食堂绑定完成，可能正常拉菜单，或被解绑
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/09
==================================================================================*/
func write_plate_site_work_process() {
	//从配置数据库读取菜单信息
	// cmenuMsg := C.sqlite_read_menuMsg_from_config_db()
	// deviceMsg.Menu_ver = int64(cmenuMsg.menu_ver)        //当前菜单版本
	// deviceMsg.NewMenu_ver = int64(cmenuMsg.new_menu_ver) //需更新的菜单版本
	debug_printf("当前的菜单版本 = %v \n", deviceMsg.Menu_ver)
	debug_printf("需要更新的版本 = %v \n", deviceMsg.NewMenu_ver)
	if deviceMsg.NewMenu_ver > deviceMsg.Menu_ver {
		debug_printf("有新菜单需要更新 \n")
		//消息队列发送 "菜单开始获取" 到 QT （QT停止写盘以及数据库的操作，关闭已打开的数据库）
		C.aws_send_menu_status_to_qt(C.int(START_GET_MENU), 0)
		//获取新菜单之前先清空旧的菜单数据库
		write_plate_clear_menu()
		//重新从美餐后台获取新的菜单
		err := write_plate_http_get_stack_menu("") //更新菜单
		if err != nil {
			debug_printf("菜单更新失败 \n")
			//消息队列发送菜单 "获取失败" 到 QT
			C.aws_send_menu_status_to_qt(C.int(GET_STATUS_FAIL), 0)
		} else {
			deviceMsg.Menu_ver = deviceMsg.NewMenu_ver //当前菜单更新成新菜单版本
			write_plate_update_menuMsg_to_config_db()  //配置数据库修改当前菜单版本为已更新的菜单版本
			//上报 IOT 菜单已更新完成
			C.set_aws_iot_report_menuUpdateTime()
			debug_printf("菜单更新成功 \n")
			//消息队列发送菜单 "获取成功" 到 QT
			C.aws_send_menu_status_to_qt(C.int(GET_STATUS_OK), 100)
		}
	}
}

/*==================================================================================
* 函 数 名： write_plate_unbind_work_process
* 参    数：
* 功能描述:  写盘器请求后台 解绑写盘器 API，返回成功后清除自身绑定状态
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/09
==================================================================================*/
func write_plate_unbind_work_process() {
	write_plate_http_site_unbind("")
}

/*==================================================================================
* 函 数 名： write_plate_updata_dev_status
* 参    数：
* 功能描述:  C 代码调用 更改golang 写盘器状态
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/09
==================================================================================*/
//export write_plate_updata_dev_status
func write_plate_updata_dev_status(status int) {
	deviceMsg.Status = status
}

/*==================================================================================
* 函 数 名： write_plate_set_config_wifi
* 参    数：
* 功能描述:  C 代码调用 开始设置WiFi
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/08/09
==================================================================================*/
//export write_plate_set_config_wifi
func write_plate_set_config_wifi(setWifiFlag int) {
	wPSetWifiFlag = setWifiFlag
}

/*==================================================================================
* 函 数 名： write_plate_updata_restaurantID
* 参    数：
* 功能描述:  C 代码调用 更改golang 写盘器餐厅ID
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/09
==================================================================================*/
//export write_plate_updata_restaurantID
func write_plate_updata_restaurantID(id int) {
	deviceMsg.RestaurantID = id
}

/*==================================================================================
* 函 数 名： write_plate_updata_menu_version
* 参    数：
* 功能描述:  C 代码调用 更改golang 写盘器需要更新的菜单版本
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/09
==================================================================================*/
//export write_plate_updata_menu_version
func write_plate_updata_menu_version(menuversion int64, newMenuVersion int64) {
	deviceMsg.Menu_ver = menuversion
	deviceMsg.NewMenu_ver = newMenuVersion
}

/*==================================================================================
* 函 数 名： write_plate_set_blue_scan
* 参    数：
* 功能描述:  C代码消息队列调用开始蓝牙搜索
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/29
==================================================================================*/

//export write_plate_set_blue_scan
func write_plate_set_blue_scan() {
	currentTime := time.Now()
	fmt.Println("wifi配置开始时间 = ", currentTime)
	cmd := exec.Command("/bin/sh", "-c", "ifconfig wlan0 down")
	if err := cmd.Start(); err != nil { // 运行命令
		fmt.Println(err)
	}
	// if err := cmd.Wait(); err != nil {
	// 	fmt.Println("wait:", err.Error())
	// }

	blueflag = true
}

/*==================================================================================
* 函 数 名： set_start_get_ntp
* 参    数：
* 功能描述:  C代码调用获取开始获取ntp时间
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/29
==================================================================================*/
//export set_start_get_ntp
func set_start_get_ntp() {
	ntpflag = true
	ntpWifiCheckFlag = true //wifi测试不是配网无需重启进程
	wPSetWifiFlag = 1
}

/*==================================================================================
* 函 数 名： write_plate_main_task
* 参    数：
* 功能描述:  写盘器主任务根据设备状态做相应的任务 工厂初始化，现场绑定食堂，获取菜单，解绑
* 返 回 值： 设备id
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/9
==================================================================================*/
func write_plate_main_task() {
	// Status := C.sqlite_read_device_satus() //从配置数据库读取设备状态
	// deviceMsg.Status = int(Status)

	debug_printf("设备状态 = %d \n", deviceMsg.Status)

	//根据设备状态执行相应的流程
	switch deviceMsg.Status {
	case INIT_STATUS: //生产状态等待工厂绑定
		if netConnectStatus == true { //联网成功后连接每餐后台获取iot证书文件
			write_plate_init_process()
		}
	case WAIT_TOPIC_STATUS: //证书获取成功，等待订阅，C代码起了线程会根据状态去完成相关订阅
		write_plate_init_iot_process()
	case FACTORY_BIND_OK_STATUS: //出厂绑定完成获取到sn码等待现场食堂绑定（解绑回到此状态）
		write_plate_site_bing_process()
	case SITE_BIND_OK_STATUS: //工作状态正常更新菜单
		write_plate_site_work_process()
	case LOCAL_UNBIND_STATUS: //本地已解绑后台未解绑，此状态需一直上传解绑状态到后台直到收到后台解绑回复
		write_plate_unbind_work_process()
	default:
	}
}
