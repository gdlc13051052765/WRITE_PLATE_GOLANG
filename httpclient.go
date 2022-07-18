package main

/*
#include <stdio.h>
#include "rewrCardTask.h"
#include "sqliteTask.h"
#include "msgTask.h"
#include "cAppTask.h"
#include "awsIotTask.h"
#include "readTxt.h"
#cgo CFLAGS: -I./
#cgo LDFLAGS: -L./ -lsqlite3 -lrfal_st25r3916 -lst25_api -lwificonfig -lm
*/
import "C"
import (
	"crypto/tls"
	"encoding/json"
	"errors"
	"fmt"
	"io/ioutil"

	//"log"
	"bytes"
	"net/http"
	"strconv"
	"strings"
	"time"

	"github.com/mozillazg/go-pinyin" //汉字转拼音
)

var pIpAddr _IpMessage //ip地址信息
var pDevMsg _DevMsgCon //设备信息
var pToken string      //token信息

// var devicetype string = "cardWriterV2" //写盘器设备类型
// var subIP string = "::1"               //""
// var version string = "v1.2.3"          //设备硬件版本号
// var closetid int                       //设备id
// var uuid string                        //uuid
// var sn string                          //设备sn号印刷在设备背面

//设备信息
type DeviceMsgSt struct {
	Shadow_name  string //shadow 名字
	Shadow_id    string //shadow clientid
	Devicetype   string //写盘器设备类型
	SubIP        string //""
	HardVersion  string //硬件版本
	Version      string //设备软件件版本号
	VersionBak   string //设备软件件版本号备份
	Menu_ver     int64  //菜单版本
	NewMenu_ver  int64  //需要更新的菜单版本
	Menu_level   int    //菜单等级
	Indent_code  int    //美餐识别码
	Id           int    //设备id
	RestaurantID int    //餐厅id
	Uuid         string //uuid
	Sn           string //设备sn号印刷在设备背面
	Status       int    //设备当前状态 生产=0，出场状态（解绑完成）=1，现场绑定完成=2，本地解绑后台未解绑=3
}

/***************************************菜单json结构体 start****************************************/

//dishes餐品结构体
type DishesSt struct {
	Id         int    `json:"id"`         //餐品ID
	Name       string `json:"name"`       //餐品名称
	UpdateTime int64  `json:"updateTime"` //更新时间  Unix time
}

//opentime结构体
type OpentimeSt struct {
	From int `json:"from"` // 从 00:00 开始的秒数, 28800 表示 08:00
	To   int `json:"to"`   //结束时间
}

//menus结构体
type MenusSt struct {
	Name         string     `json:"name"`         // 菜单名称
	MealPlanName string     `json:"mealPlanName"` //结束时间
	Date         string     `json:"date"`         // 更新时间
	OpenTime     OpentimeSt `json:"openTime"`     //opentime结构体
	Dishes       []DishesSt `json:"dishes"`       // 餐品
}

//json data域结构体
type dataSt struct {
	Menus []MenusSt `json:"menus"` //body数据
}

//json body数据
type Response struct {
	ResultCode        string `json:"resultCode"`        //返回结果
	ResultDescription string `json:"resultDescription"` //返回结果
	Data              dataSt `json:"data"`              //body数据
}

/*****************************菜单json结构体 end***********************************/
//数据库内容
type menuData struct {
	id        int    //菜单索引
	prev_menu string //上一级菜单
	next_menu string //下一级菜单
	grade     int    //菜单当前等级
	context   string //菜单内容
	spell     string //拼音首字母
	dish_id   int    //餐品ID
}

//工厂初始化获取iot证书uuid信息结构体
type awsIotInitSt struct {
	ResultCode        string `json:"resultCode"`        //返回结果
	ResultDescription string `json:"resultDescription"` //返回结果
	Data              struct {
		Id          int    `json:"id"`          //id
		CafeteriaID int    `json:"cafeteriaID"` //id
		Type        string `json:"type"`
		Uuid        string `json:"uuid"` //clients id
		Ip          string `json:"ip"`
		SubIP       string `json:"subIP"`
		Removed     bool   `json:"removed"`
		Version     string `json:"version"`
		SnID        int    `json:"snID"`
		Status      string `json:"status"`
		RomVersion  int    `json:"romVersion"`
		SubType     string `json:"subType"`
		IotInfo     struct {
			DeviceID       string `json:"deviceID"`  //clients id
			ThingName      string `json:"thingName"` //shadow 名字
			ThingTypeName  string `json:"thingTypeName"`
			ThingGroupName string `json:"thingGroupName"`
			PolicyName     string `json:"policyName"`
			CertificateID  string `json:"certificateID"`
			CertificateARM string `json:"certificateARM"`
			CertificatePEM string `json:"certificatePEM"` //证书
			KeyPair        struct {
				PrivateKey string `json:"privateKey"` //私钥
				PublicKey  string `json:"publicKey"`
			} `json:"keyPair"`
			ApplyState      string `json:"applyState"`
			EnableCertToken bool   `json:"enableCertToken"`
			CreatedTime     int64  `json:"createdTime"`
			UpdatedTime     int64  `json:"updatedTime"`
			ExpireTime      int64  `json:"expireTime"`
			Version         int64  `json:"version"`
		} `json:"iotInfo"`
		Ready bool `json:"ready"`
	} `json:"data"` //body数据
}

/********************************菜单json结构体 end*******************************************/

//初始菜单等级名称
var menu_lev string = "menu_lev1"

//设备信息
var deviceMsg DeviceMsgSt

//当前菜单等级
var lay_stack int = 0
var lay_stackBak int = 0

//本机测试服务器地址 或者美餐服务器地址
var TEST_WORK_FLAG bool = false //true 本机测试服务器地址；false 美餐后台

//美餐后台 URl
//var mei_can_server_url string = "http://test6-baseinfo.meican.com"

//美餐后台 URl
var mei_can_server_url string = "https://baseinfo.meican.com"

//现场绑定token
var siteBindToken string

//菜单总长度
var menuToalLength int = 0

//dishes的个数s
var toalDishesNumber int = 0

//绑定接口id
var bindRestaurantID int = 0

/*==================================================================================
* 函 数 名： write_plate_insert_data_to_menu_db
* 参    数： 字符串
* 功能描述:  创建菜品索引数据库
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/5/20
==================================================================================*/
func write_plate_insert_data_to_menu_db(dbname string, menust menuData) {
	var cmeunData C.C_MenuDataSt

	cmeunData.dbname = C.CString(dbname)             //数据库名字
	cmeunData.premenu = C.CString(menust.prev_menu)  //前数据库索引
	cmeunData.nextmenu = C.CString(menust.next_menu) //后数据库索引
	cmeunData.grade = C.int(menust.grade)            //菜单等级
	cmeunData.context = C.CString(menust.context)    //菜单内容
	cmeunData.spell = C.CString(menust.spell)        //拼音首字母
	cmeunData.dish_id = C.int(menust.dish_id)        //餐品ID

	C.sqlite_insert_data_to_menu_db(cmeunData)
}

/*==================================================================================
* 函 数 名： write_plate_read_msg_from_config_sqlite
* 参    数：
* 功能描述:  从配置数据库读取设备信息
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/5/20
==================================================================================*/
func write_plate_read_msg_from_config_sqlite() {
	//var cdevMsg C.C_DevMsgSt
	// var cmenuMsg C.C_menuMsgSt

	//从配置数据库读取设备信息
	cdevMsg := C.sqlite_read_devMsg_from_config_db()
	deviceMsg.Uuid = C.GoString(cdevMsg.uuid)               //uuid
	deviceMsg.Sn = C.GoString(cdevMsg.sn)                   //设备SN码
	deviceMsg.HardVersion = C.GoString(cdevMsg.hardVersion) // 硬件版本
	deviceMsg.Version = C.GoString(cdevMsg.version)         // 固件版本
	deviceMsg.VersionBak = C.GoString(cdevMsg.versionBak)   // 固件版本备份
	deviceMsg.Id = int(cdevMsg.id)                          //设备id
	deviceMsg.Indent_code = int(cdevMsg.indent_code)        //美餐识别码
	deviceMsg.Status = int(cdevMsg.status)                  //设备状态
	deviceMsg.RestaurantID = int(cdevMsg.restaurantID)      //餐厅ID

	debug_printf("deviceMsg.HardVersion = %s \n", deviceMsg.HardVersion)
	debug_printf("deviceMsg.Version = %s \n", deviceMsg.Version)
	debug_printf("deviceMsg.VersionBak = %s \n", deviceMsg.VersionBak)
	debug_printf("deviceMsg.Uuid = %s \n", deviceMsg.Uuid)
	debug_printf("deviceMsg.Sn = %s \n", deviceMsg.Sn)
	debug_printf("deviceMsg.Id = %d \n", deviceMsg.Id)
	debug_printf("deviceMsg.Indent_code = %d \n", deviceMsg.Indent_code)
	debug_printf("deviceMsg.Status = %d \n", deviceMsg.Status)
	debug_printf("deviceMsg.RestaurantID = %d \n", deviceMsg.RestaurantID)

	if backUpAppFlag == false {
		if strings.Compare(deviceMsg.Version, deviceMsg.VersionBak) == 0 {
			debug_printf("版本一致无需上报\n")
		} else {
			debug_printf("版本不一致需要上报固件更新结果\n")
			if strings.Compare(version, deviceMsg.VersionBak) == 0 { //备份临时版本跟新启动的软件版本一致
				C.set_flag_report_iot_update_ok(C.int(0))
				//C.set_aws_iot_report_romVersion()
				debug_printf("固件更新成功 \n")
			} else {
				C.set_flag_report_iot_update_ok(C.int(1))
				debug_printf("固件更新失败 \n")
			}
		}
	} else { //备份程序
		C.sqlite_update_version_config_db(C.CString(version))
	}

	//从配置数据库读取菜单信息
	cmenuMsg := C.sqlite_read_menuMsg_from_config_db()
	deviceMsg.Menu_ver = int64(cmenuMsg.menu_ver)        //当前菜单版本
	deviceMsg.NewMenu_ver = int64(cmenuMsg.new_menu_ver) //需更新的菜单版本
	deviceMsg.Menu_level = int(cmenuMsg.menu_level)      //菜单等级

	debug_printf("deviceMsg.menu_ver = %v \n", deviceMsg.Menu_ver)
	debug_printf("deviceMsg.new_menu_ver = %v \n", deviceMsg.NewMenu_ver)
	debug_printf("deviceMsg.menu_level = %d \n", deviceMsg.Menu_level)
}

/*==================================================================================
* 函 数 名： write_plate_update_devMsg_to_config_db
* 参    数：
* 功能描述:  更新配置数据库设备信息
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/5/20
==================================================================================*/
func write_plate_update_devMsg_to_config_db() {
	//更新配置数据库设备信息
	var cdevMsg C.C_DevMsgSt

	cdevMsg.uuid = C.CString(deviceMsg.Uuid) //uuid
	cdevMsg.sn = C.CString(deviceMsg.Sn)     //sn码
	cdevMsg.id = C.int(deviceMsg.Id)         //设备id
	cdevMsg.status = C.int(deviceMsg.Status) //设备状态

	C.sqlite_update_devMsg_to_config_db(cdevMsg)
}

/*==================================================================================
* 函 数 名： write_plate_update_shadowMsg_to_config_db
* 参    数：
* 功能描述:  更新配置数据库shadow信息
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/5/20
==================================================================================*/
func write_plate_update_shadowMsg_to_config_db() {
	//更新配置数据库shadow信息
	var cdevMsg C.C_ShadowMsgSt

	cdevMsg.name = C.CString(deviceMsg.Shadow_name)   //AWS shadow 名字
	cdevMsg.clientid = C.CString(deviceMsg.Shadow_id) //AWS shadow client id

	C.sqlite_update_shadowMsg_to_config_db(cdevMsg)
}

/*==================================================================================
* 函 数 名： write_plate_update_menuMsg_to_config_db
* 参    数：
* 功能描述:  更新配置数据库菜单信息
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/5/20
==================================================================================*/
func write_plate_update_menuMsg_to_config_db() {
	//更新配置数据库菜单版本菜单等级
	var cmenuMsg C.C_menuMsgSt

	cmenuMsg.new_menu_ver = C.longlong(deviceMsg.NewMenu_ver) //菜单版本
	cmenuMsg.menu_ver = C.longlong(deviceMsg.Menu_ver)        //菜单版本
	cmenuMsg.menu_level = C.int(deviceMsg.Menu_level)         //菜单等级

	C.sqlite_update_menuMsg_to_config_db(cmenuMsg)
}

/*==================================================================================
* 函 数 名： write_plate_write_menu_sqlite
* 参    数： 字符串
* 功能描述:  菜品信息写入数据库
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/5/20
==================================================================================*/
func write_plate_write_menu_sqlite(res string) {
	//解析json数据体
	var r dataSt
	err := json.Unmarshal([]byte(res), &r)
	if err != nil {
		debug_printf("err was %v", err)
	}
	//menus菜单层
	for i := 0; i < len(r.Menus); i++ {
		debug_printf("Dishes num = %d \n", len(r.Menus[i].Dishes))                                            //菜单里面菜品的个数
		debug_printf("Menus name = %s \n", r.Menus[i].Name)                                                   //打印菜单名称                                      //打印菜单里面Dishes的个数
		debug_printf("start time = %d ; stop time = %d \n", r.Menus[i].OpenTime.From, r.Menus[i].OpenTime.To) //开始结束的秒数
		for j := 0; j < len(r.Menus[i].Dishes); j++ {                                                         //dishs菜品层
			debug_printf("id = %d ; name = %s \n", r.Menus[i].Dishes[j].Id, r.Menus[i].Dishes[j].Name) //打印菜品名称 ，ID
			//汉字转拼音
			b := pinyin.Pinyin(r.Menus[i].Dishes[j].Name, pinyin.NewArgs())
			debug_printf("spell = %s \n", strings.ToUpper(b[0][0][0:1])) //小写转大写
		}
	}
}

// 发送POST请求
// url：         请求地址
// data：        POST请求提交的数据
// token 请求体格式，如：定时更新
// content：     请求放回的内容
func http_post(url string, data map[string]interface{}, token string) (content string, err error) {
	jsonStr, _ := json.Marshal(data)
	req, err := http.NewRequest("POST", url, bytes.NewBuffer(jsonStr))
	if err != nil {
		fmt.Println("resquest err\n")
	}
	//设置header
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Cookie", "name=anny")
	req.Header.Set("Connection", "keep-alive")
	req.Header.Set("x-meican-auth-device", deviceMsg.Uuid)
	// req.Header.Set("clientID", "D4784848C17E9802134C7A9B535DB5B2")
	// req.Header.Set("clientSecret", "482042FD95A175BB62306A987BE3CED8")

	// fmt.Printf("x-meican-auth-device = %s\n", deviceMsg.Uuid)
	// fmt.Printf("clientID = %s\n", "D4784848C17E9802134C7A9B535DB5B2")
	// fmt.Printf("clientSecret = %s\n", "482042FD95A175BB62306A987BE3CED8")

	req.Header.Set("clientID", "C76FBFF0AA54D8C4D4017FFAE6AF2AE8")
	req.Header.Set("clientSecret", "2AB04EDA814820CA97037C55A911CA1F")

	fmt.Printf("x-meican-auth-device = %s\n", deviceMsg.Uuid)
	fmt.Printf("clientID = %s\n", "C76FBFF0AA54D8C4D4017FFAE6AF2AE8")
	fmt.Printf("clientSecret = %s\n", "2AB04EDA814820CA97037C55A911CA1F")

	if strings.Index(url, "addEPlateWriterV2") > 0 {
		tokenstr := fmt.Sprintf("bearer %s", siteBindToken)
		fmt.Printf("Authorization = %s\n", tokenstr)
		req.Header.Set("Authorization", tokenstr)
	}
	//https 跳过认证

	tr := &http.Transport{
		TLSClientConfig: &tls.Config{InsecureSkipVerify: true},
	}
	client := &http.Client{Transport: tr, Timeout: 4 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return content, err
	}

	defer resp.Body.Close()
	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		fmt.Println("ReadAll err\n")
	}
	// fmt.Println(string(body))
	content = string(body)
	return content, err
}

// 发送GET请求
// url：         请求地址
// data：        GET请求提交的数据
// token 请求体格式，如：定时更新
// content：     请求放回的内容
func http_get(url string, data map[string]interface{}, token string) (content string, err error) {
	jsonStr, _ := json.Marshal(data)
	req, err := http.NewRequest("GET", url, bytes.NewBuffer(jsonStr))
	if err != nil {
		fmt.Println("resquest err\n")
	}
	//设置header
	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Cookie", "name=anny")
	req.Header.Set("Connection", "keep-alive")
	req.Header.Set("x-meican-auth-device", deviceMsg.Uuid)

	tr := &http.Transport{
		TLSClientConfig: &tls.Config{InsecureSkipVerify: true},
	}
	client := &http.Client{Transport: tr, Timeout: 4 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return content, err
	}

	defer resp.Body.Close()
	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		fmt.Println("ReadAll err\n")
	}
	// fmt.Println(string(body))
	content = string(body)
	return content, err
}

// 发送POST请求
// url：         请求地址
// data：        POST请求提交的数据
// token 请求体格式，如：定时更新
// content：     请求放回的内容
func test_http_post(url string, data map[string]interface{}, token string) (content string, err error) {
	jsonStr, _ := json.Marshal(data)
	req, err := http.NewRequest("POST", url, bytes.NewBuffer(jsonStr))
	if err != nil {
		fmt.Println("resquest err\n")
	}

	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Cookie", "name=anny")
	req.Header.Set("Connection", "keep-alive")
	req.Header.Set("x-meican-auth-device", deviceMsg.Uuid)
	req.Header.Set("clientID", "D4784848C17E9802134C7A9B535DB5B2")
	req.Header.Set("clientSecret", "482042FD95A175BB62306A987BE3CED8")
	tokenstr := fmt.Sprintf("bearer %s", siteBindToken)
	req.Header.Set("Authorization", tokenstr)
	//req.Header.Set("Authorization", "bearer 0df65585a2a543d78f602c7edfce49b8")

	tr := &http.Transport{
		TLSClientConfig: &tls.Config{InsecureSkipVerify: true},
	}
	client := &http.Client{Transport: tr, Timeout: 4 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return content, err
	}

	defer resp.Body.Close()
	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		fmt.Println("ReadAll err\n")
	}
	//fmt.Println(string(body))
	content = string(body)
	return content, err
}

// 发送POST请求
// url：         请求地址
// data：        POST请求提交的数据
// token 请求体格式，如：定时更新
// content：     请求放回的内容
func test_http_get(url string, data map[string]interface{}, token string) (content string, err error) {
	jsonStr, _ := json.Marshal(data)
	req, err := http.NewRequest("GET", url, bytes.NewBuffer(jsonStr))
	if err != nil {
		fmt.Println("resquest err\n")
	}

	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Cookie", "name=anny")
	req.Header.Set("Connection", "keep-alive")
	req.Header.Set("x-meican-auth-device", deviceMsg.Uuid)
	req.Header.Set("clientID", "D4784848C17E9802134C7A9B535DB5B2")
	req.Header.Set("clientSecret", "482042FD95A175BB62306A987BE3CED8")
	tokenstr := fmt.Sprintf("bearer %s", siteBindToken)
	req.Header.Set("Authorization", tokenstr)
	//req.Header.Set("Authorization", "bearer 0df65585a2a543d78f602c7edfce49b8")

	tr := &http.Transport{
		TLSClientConfig: &tls.Config{InsecureSkipVerify: true},
	}
	client := &http.Client{Transport: tr, Timeout: 4 * time.Second}
	resp, err := client.Do(req)
	if err != nil {
		return content, err
	}

	defer resp.Body.Close()
	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		fmt.Println("ReadAll err\n")
	}
	//fmt.Println(string(body))
	content = string(body)
	return content, err
}

/*==================================================================================
* 函 数 名： http_client_parameter_init
* 参    数：ip地址信息 设备信息
* 功能描述:  http参数初始化 设备信心 IP地址信息传入
* 返 回 值： token信息:tokenMsg；
* 备    注： None
* 作    者： lc
* 创建时间： 2021/4/14
==================================================================================*/
func http_client_parameter_init(mIpAddr _IpMessage, mDevMsg _DevMsgCon) {
	pIpAddr.routeip = mIpAddr.routeip //远端ip
	pIpAddr.port = mIpAddr.port       //远端端口

	pDevMsg.clientID = mDevMsg.clientID         //客户id
	pDevMsg.clientSecret = mDevMsg.clientSecret //客户密钥
}

/*==================================================================================
* 函 数 名： write_plate_http_devices_init
* 参    数： 请求参数:type设备类型 ip地址信息:mIpstr；http请求接口:tokenUrl
* 功能描述:  后台请求设备id
* 返 回 值： 设备id
* 备    注： None
* 作    者： lc
* 创建时间： 2021/4/14
==================================================================================*/
func write_plate_http_devices_init(tokenUrl string) error {
	result := make(map[string]interface{})
	var res string
	var err error
	result["type"] = "cardWriterV2"          //设备类型
	result["romVersion"] = deviceMsg.Version //固件版本

	if TEST_WORK_FLAG == true { //发送到本机测试服务器
		Urltest := fmt.Sprintf("http://%s:%s%s", pIpAddr.routeip, pIpAddr.port, "/devices/init/v3") //pc测试端口
		debug_printf("Urltest = %v\n", Urltest)
		res, err = test_http_post(Urltest, result, "")
	} else { //发送到美餐后台服务器
		Url := fmt.Sprintf("%s%s", mei_can_server_url, "/devices/init/v3")
		debug_printf("meican ser = %v\n", Url)
		res, err = http_post(Url, result, "")
	}

	//解析json数据体
	var r awsIotInitSt
	err = json.Unmarshal([]byte(res), &r)
	if err != nil {
		debug_printf("err was %v\n", err)
	} else {
		debug_printf("ResultCode =  %s \n", r.ResultCode)
		if r.ResultCode == "OK" {
			debug_printf("deviceMsg.Uuid = %s \n", r.Data.Uuid)
			debug_printf("deviceID =  %s \n", r.Data.IotInfo.DeviceID)
			debug_printf("thingName =  %s \n", r.Data.IotInfo.ThingName)
			// debug_printf("certificatePEM =  %s \n", r.Data.IotInfo.CertificatePEM)
			// debug_printf("privateKey =  %s \n", r.Data.IotInfo.KeyPair.PrivateKey)
			deviceMsg.Id = r.Data.Id                         //获取设备id
			deviceMsg.Uuid = r.Data.Uuid                     //获取uuid
			deviceMsg.Status = WAIT_TOPIC_STATUS             //更改设备状态证书获取成功等待IOT订阅
			deviceMsg.Shadow_name = r.Data.IotInfo.ThingName //shadow 名字
			deviceMsg.Shadow_id = r.Data.IotInfo.DeviceID    //shadow clientid

			make_mctid_qr_code(deviceMsg.Uuid) //生成二维码图片QT调用
			//获取当前路径
			// dir, _ := os.Getwd()
			// debug_printf("当前路径：\n", dir)
			filename := fmt.Sprintf("%s/certs/cert.pem", "/home/meican")
			err = write_file_data(filename, r.Data.IotInfo.CertificatePEM) //创建并写入证书文件
			filename = fmt.Sprintf("%s/certs/privkey.pem", "/home/meican")
			err = write_file_data(filename, r.Data.IotInfo.KeyPair.PrivateKey) //创建并写入私钥文件
			//更新配置数据库id，uuid，设备状态
			write_plate_update_devMsg_to_config_db()
			//更新配置数据库shadow信息
			write_plate_update_shadowMsg_to_config_db()

			// netstatus := 0
			// C.msg_send_net_connect_status(C.int(netstatus)) //消息队列发送联网指令到QT
			// // time.Sleep(3 * time.Second)

			C.aws_send_change_status_to_qt(C.int(1)) //发送更改设备状态

			C.update_aws_iot_dev_status(WAIT_TOPIC_STATUS) //iot 的设备状态也相应的更新
		} else {
			err = errors.New("result code error")
		}
	}
	return err
}

/*==================================================================================
* 函 数 名： write_plate_http_site_bind
* 参    数： 现场绑定SN
* 功能描述:  后台请求设备id
* 返 回 值： 设备id
* 备    注： None
* 作    者： lc
* 创建时间： 2021/4/14
==================================================================================*/
func write_plate_http_site_bind(tokenUrl string) error {
	var res string
	var err error
	result := make(map[string]interface{})
	result["uuid"] = deviceMsg.Uuid //body 传入uuid
	//str1 := strconv.Itoa(deviceMsg.RestaurantID)
	str1 := strconv.Itoa(bindRestaurantID)
	urlapi := fmt.Sprintf("/admin/restaurant/%s/devices/addEPlateWriterV2", str1)

	if TEST_WORK_FLAG == true { //发送到测试pc端口
		Urltest := fmt.Sprintf("http://%s:%s%s", pIpAddr.routeip, pIpAddr.port, urlapi) //pc测试端口
		debug_printf("Urltest = %v\n", Urltest)
		res, err = test_http_post(Urltest, result, "")
	} else { //发送到美餐后台服务器
		Url := fmt.Sprintf("%s%s", mei_can_server_url, urlapi)
		debug_printf("meican ser = %v\n", Url)
		res, err = http_post(Url, result, "")
	}
	//创建一个map
	m := make(map[string]interface{}, 3)
	err = json.Unmarshal([]byte(res), &m) //第二个参数要地址传递
	if err != nil {
		fmt.Println("err = ", err)
		return err
	}

	debug_printf("res = %v\n", res)
	if m["resultCode"] == "OK" || m["resultDescription"] == "SUCCESS" {
		//debug_printf("resultData = %T value = %v\n", m["resultData"], m["resultData"])
	} else {
		fmt.Printf("resultCode = %v, resultDescription = %v \n", m["resultCode"], m["resultDescription"])
		err = errors.New("result code error")
		return err
	}

	// //更新配置数据库
	//deviceMsg.Status = SITE_BIND_OK_STATUS //设备状态更新为现场绑定食堂完成，并写入配置数据库
	// write_plate_update_devMsg_to_config_db()
	return err
}

/*==================================================================================
* 函 数 名： write_plate_http_site_unbind
* 参    数：
* 功能描述:  后台请求解绑写盘器
* 返 回 值： 设备id
* 备    注： None
* 作    者： lc
* 创建时间： 2021/4/14
==================================================================================*/
func write_plate_http_site_unbind(tokenUrl string) error {
	var res string
	var err error
	result := make(map[string]interface{})
	result["uuid"] = deviceMsg.Uuid //body 传入uuid
	str1 := strconv.Itoa(deviceMsg.RestaurantID)
	urlapi := fmt.Sprintf("/admin/restaurant/%s/devices/cardWriterV2/remove", str1)

	if TEST_WORK_FLAG == true { //发送到测试pc端口
		Urltest := fmt.Sprintf("http://%s:%s%s", pIpAddr.routeip, pIpAddr.port, urlapi) //pc测试端口
		debug_printf("Urltest = %v\n", Urltest)
		res, err = test_http_post(Urltest, result, "")
	} else { //发送到美餐后台服务器
		Url := fmt.Sprintf("%s%s", mei_can_server_url, urlapi)
		debug_printf("meican ser = %v\n", Url)
		res, err = http_post(Url, result, "")
	}
	//创建一个map
	m := make(map[string]interface{}, 3)
	err = json.Unmarshal([]byte(res), &m) //第二个参数要地址传递
	if err != nil {
		fmt.Println("err = ", err)
		return err
	}

	debug_printf("res = %v\n", res)
	if m["resultCode"] == "OK" || m["resultDescription"] == "SUCCESS" {
		//debug_printf("resultData = %T value = %v\n", m["resultData"], m["resultData"])
	} else {
		fmt.Printf("resultCode = %v, resultDescription = %v \n", m["resultCode"], m["resultDescription"])
		err = errors.New("result code error")
		return err
	}
	//更新配置数据库
	deviceMsg.Status = FACTORY_BIND_OK_STATUS //设备状态更新为现场绑定完成状态（解绑状态），并写入配置数据库
	C.sqlite_update_dev_status_config_db(C.int(deviceMsg.Status))
	//菜单信息归 0
	deviceMsg.NewMenu_ver = 0
	deviceMsg.Menu_ver = 0
	deviceMsg.Menu_level = 0
	write_plate_update_menuMsg_to_config_db()
	write_plate_clear_menu() //清空菜单数据库
	return err
}

/*==================================================================================
* 函 数 名： jsonArrayParse,jsonObjectParse
* 参    数：
* 功能描述:  json递归解析
* 返 回 值： 设备id
* 备    注： None
* 作    者： lc
* 创建时间： 2021/5/13
==================================================================================*/
func jsonArrayParse(vv []interface{}, lev int) {
	for i, u := range vv {
		switch vv1 := u.(type) {
		case string:
			//fmt.Println(i, "[string_]:", u)
		case float64:
			fmt.Println(i, "[float64_]:", u)
		case bool:
			fmt.Println(i, "[bool_]:", u)
		case nil:
			fmt.Println(i, "[nil_]:", u)
		case []interface{}:
			//fmt.Println(i, "[array_]:", u)
			jsonArrayParse(vv1, lev)
		case interface{}:
			//fmt.Println(i, "[interface_]:", u)
			//根据当前解析的菜单等级 lev 查找数据库名字对应的 “_”的位置
			var addnum int = 0
			for kk, v := range menu_lev {
				if string(v) == "_" {
					if addnum == lev {
						addnum = kk
						break
					}
					addnum += 1
				}
			}
			menu_lev = menu_lev[0:addnum]       //截取当前层数据库表名字
			menu_lev += "_" + strconv.Itoa(i+1) //新的数据库名字
			//根据当前菜单等级创建数据库并将name写入上一级数据库
			m1 := u.(map[string]interface{})
			debug_printf("name = %s \n", m1["name"])
			//debug_printf("menu_lev = %s \n", menu_lev)
			if m1["id"] == nil { //由是否包含“id”判断是否是最底层菜单，如果是则无需创建数据库
				sqliteDb := C.CString(menu_lev)
				C.sqlite_create_menu_db(sqliteDb) //根据当前等级创建相应的数据库
			}

			/************************菜单信息写入数据库 start*********************************/
			var menust menuData
			if lev == 1 { //第一级主菜单无上一级菜单索引
				menust.prev_menu = "" //字段内容设为空
			} else {
				menubak := menu_lev[0:strings.LastIndex(menu_lev, "_")]        //上一级菜单
				menust.prev_menu = menu_lev[0:strings.LastIndex(menubak, "_")] //上上一级菜单
			}
			if m1["id"] != nil {
				menust.dish_id = int(m1["id"].(float64)) //菜品id
				menust.next_menu = ""                    //最后一次菜单无下级菜单索引
			} else {
				menust.next_menu = menu_lev //下一级菜单
				menust.dish_id = -1         //无需dish_id字段数据的默认设置成 -1
			}
			if m1["nameInitial"] != nil { //拼音首字母
				menust.spell = m1["nameInitial"].(string)
			}
			if m1["name"] != nil {
				menust.grade = lev                   //菜单等级
				menust.context = m1["name"].(string) //菜单名字
				//汉字转拼音
				// b := pinyin.Pinyin(menust.context, pinyin.NewArgs()) //汉字转拼音
				// menust.spell = strings.ToUpper(b[0][0][0:1])
				write_plate_insert_data_to_menu_db(menu_lev[0:strings.LastIndex(menu_lev, "_")], menust) //菜单写入上一级数据库
			}
			/************************菜单信息写入数据库 end***********************************/
			jsonObjectParse(m1, lev)
		default:
			fmt.Println("", i, "[type?_]", u, ",", vv1)
		}
	}
}

var updateProcess int = 0 //菜单更新进度
func jsonObjectParse(f interface{}, lev int) {
	m := f.(map[string]interface{})
	for k, v := range m {
		switch vv := v.(type) {
		case string:
			fmt.Println(k, "[string]:", vv)
		case float64:
			fmt.Println(k, "[float64]:", vv)
		case bool:
			fmt.Println(k, "[bool]:", vv)
		case nil:
			fmt.Println(k, "[nil]:", vv)
		case []interface{}:
			//fmt.Println(k, "[array]:", vv)
			lev += 1           //层叠结构加1
			if k == "dishes" { //用 "dishes" 字符的个数来计算菜单更新进度
				updateProcess++
				process := (updateProcess * 100) / toalDishesNumber
				C.aws_send_menu_status_to_qt(C.int(GET_STATUS_PROCESS), C.int(process))
			}
			lay_stackBak = lev //层叠结构备份
			menu_lev += "_" + strconv.Itoa(lev)
			jsonArrayParse(vv, lev)
		case interface{}:
			//fmt.Println(k, "[interface]:", vv)
			m1 := v.(map[string]interface{})
			jsonObjectParse(m1, lev)
		default:
			//fmt.Println(k, "[type?]", vv)
		}
	}
}

/*==================================================================================
* 函 数 名： write_plate_http_get_menu
* 参    数： 获取菜单
* 功能描述:  后台请求设备id
* 返 回 值： 设备id
* 备    注： None
* 作    者： lc
* 创建时间： 2021/5/13
==================================================================================*/
func write_plate_http_get_menu(tokenUrl string) error {
	result := make(map[string]interface{})
	//C.set_stop_write_palte_status() //菜单更新时停止写盘
	str1 := strconv.Itoa(deviceMsg.RestaurantID)
	urlapi := fmt.Sprintf("/admin/restaurant/%s/ePlateWriterDishes", str1)
	//urlapi := "/admin/restaurant/:restaurantID/ePlateWriterDishes"
	Urltest := fmt.Sprintf("http://%s:%s%s", pIpAddr.routeip, pIpAddr.port, urlapi) //pc测试端口

	//lc test 发送到测试pc端口
	debug_printf("Urltest = %v\n", Urltest)
	res, err := test_http_get(Urltest, result, deviceMsg.Uuid)

	//发送到后台服务器
	// Url := fmt.Sprintf("http://test-baseinfo.meican.com%s", urlapi)
	// res, err := http_get(Url, result, "")
	//创建一个map
	m := make(map[string]interface{}, 3)
	err = json.Unmarshal([]byte(res), &m) //第二个参数要地址传递
	if err != nil {
		fmt.Println("err = ", err)
		return err
	}
	debug_printf("res = %v\n", res)
	if m["resultCode"] == "OK" || m["resultDescription"] == "SUCCESS" {
		//debug_printf("resultData = %T value = %v\n", m["resultData"], m["resultData"])
	} else {
		fmt.Printf("resultCode = %v, resultDescription = %v \n", m["resultCode"], m["resultDescription"])
		err = errors.New("result code error")
		return err
	}
	//解析json数据体
	var r Response
	err = json.Unmarshal([]byte(res), &r)
	if err != nil {
		debug_printf("err was %v", err)
	}
	debug_printf("toal Menus num = %d \n", len(r.Data.Menus)) //打印menus的个数
	for i := 0; i < len(r.Data.Menus); i++ {                  //menus菜单层
		debug_printf("Dishes num = %d \n", len(r.Data.Menus[i].Dishes))                                                 //菜单里面菜品的个数
		debug_printf("Menus name = %s \n", r.Data.Menus[i].Name)                                                        //打印菜单名称                                      //打印菜单里面Dishes的个数
		debug_printf("start time = %d ; stop time = %d \n", r.Data.Menus[i].OpenTime.From, r.Data.Menus[i].OpenTime.To) //开始结束的秒数
		for j := 0; j < len(r.Data.Menus[i].Dishes); j++ {                                                              //dishs菜品层
			debug_printf("id = %d ; name = %s \n", r.Data.Menus[i].Dishes[j].Id, r.Data.Menus[i].Dishes[j].Name) //打印菜品名称 ，ID
			//汉字转拼音
			b := pinyin.Pinyin(r.Data.Menus[i].Dishes[j].Name, pinyin.NewArgs())
			debug_printf("spell = %s \n", strings.ToUpper(b[0][0][0:1])) //小写转大写
		}
	}
	return err
}

/*==================================================================================
* 函 数 名： write_plate_http_get_stack_menu
* 参    数： 获取层叠菜单
* 功能描述:  后台请求设备id
* 返 回 值： 设备id
* 备    注： None
* 作    者： lc
* 创建时间： 2021/5/13
==================================================================================*/
func write_plate_http_get_stack_menu(tokenUrl string) error {
	var err error
	var res string

	updateProcess = 0
	result := make(map[string]interface{})
	str1 := strconv.Itoa(deviceMsg.RestaurantID)
	urlapi := fmt.Sprintf("/admin/restaurant/%s/ePlateMenu/v2", str1)

	if TEST_WORK_FLAG == true { //发送到测试pc端口
		Urltest := fmt.Sprintf("http://%s:%s%s", pIpAddr.routeip, pIpAddr.port, urlapi) //pc测试端口
		debug_printf("Urltest = %v\n", Urltest)
		res, err = test_http_get(Urltest, result, deviceMsg.Uuid)
		menuToalLength = len(res) //菜单总长度
		debug_printf("菜单总长度 = %v\n", menuToalLength)
		toalDishesNumber = strings.Count(res, "dishes")
		debug_printf("菜单dish字符个数 = %v\n", toalDishesNumber)
	} else { //发送到美餐后台服务器
		Url := fmt.Sprintf("%s%s", mei_can_server_url, urlapi)
		debug_printf("meican server = %v\n", Url)
		res, err = http_get(Url, result, "")
		menuToalLength = len(res) //菜单总长度
		debug_printf("菜单总长度 = %v\n", menuToalLength)
		toalDishesNumber = strings.Count(res, "dishes")
		debug_printf("菜单dish字符个数 = %v\n", toalDishesNumber)
	}
	//创建一个map
	m := make(map[string]interface{}, 3)
	err = json.Unmarshal([]byte(res), &m) //第二个参数要地址传递
	if err != nil {
		fmt.Println("err = ", err)
		return err
	}
	if m["resultCode"] == "OK" || m["resultDescription"] == "SUCCESS" {
		debug_printf("resultData = %T value = %v\n", m["resultData"], m["resultData"])
	} else {
		fmt.Printf("resultCode = %v, resultDescription = %v \n", m["resultCode"], m["resultDescription"])
		err = errors.New("result code error")
		return err
	}
	//解析json数据体
	jsonStr := []byte(res)
	if strings.Index(string(jsonStr[:]), "[") == 0 {
		var f []interface{}
		err := json.Unmarshal(jsonStr, &f)
		if err != nil {
			fmt.Println(err)
		}
		jsonArrayParse(f, lay_stack)
	} else {
		var f interface{}
		err := json.Unmarshal(jsonStr, &f)
		if err != nil {
			fmt.Println(err)
		}
		jsonObjectParse(f, lay_stack)
	}
	//修改配置数据菜单信息,修改菜单层叠
	debug_printf("lay_stack = %d \n", lay_stackBak)
	deviceMsg.Menu_level = lay_stackBak
	write_plate_update_menuMsg_to_config_db()
	return err
}
