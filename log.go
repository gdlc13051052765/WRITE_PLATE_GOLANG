package main

import "C"
import (
	"fmt"
	"log"
	"os"
	"time"
)

/*==================================================================================
* 函 数 名： write_plate_write_log_task
* 参    数：
* 功能描述:  写盘器定时写log
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/29
==================================================================================*/
//export write_plate_write_IOT_log
func write_plate_write_IOT_log(iotstr *C.char) {
	var file *os.File

	//以年月日为后缀创建CPU温度频率log文件
	year := time.Now().Format("2006")
	month := time.Now().Format("01")
	day := time.Now().Format("02")
	filename := fmt.Sprintf("/home/meican/logfiles/iot-%s-%s-%s.log", year, month, day)
	if checkFileIsExist(filename) { //如果文件存在
		file, _ = os.OpenFile(filename, os.O_RDWR|os.O_APPEND, 0666) //打开文件不清空已追加方式打开，写入文件末尾
		fmt.Println("iot文件存在")
	} else {
		file, _ = os.Create(filename) //创建文件
		fmt.Println("iot文件不存在")
	}

	log.New(file, "", log.Llongfile)
	//默认会有log.Ldate | log.Ltime（日期 时间），这里重写为 日 时 文件名
	//log.SetFlags(log.Ldate | log.Ltime | log.Lshortfile) //2015/04/22 11:28:41 test.go:29: content
	log.SetFlags(log.Ldate | log.Ltime) //2015/04/22 11:28:41  content

	//write log
	log.SetOutput(file)
	str := C.GoString(iotstr)
	log.Printf(str)
	file.Close()
}

/*==================================================================================
* 函 数 名： write_plate_write_rfid_log
* 参    数：
* 功能描述:  写盘器定时写读写卡log
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/29
==================================================================================*/
//export write_plate_write_rfid_log
func write_plate_write_rfid_log(iotstr *C.char) {
	var file *os.File

	//以年月日为后缀创建CPU温度频率log文件
	year := time.Now().Format("2006")
	month := time.Now().Format("01")
	day := time.Now().Format("02")
	filename := fmt.Sprintf("/home/meican/logfiles/rfid-%s-%s-%s.log", year, month, day)

	if checkFileIsExist(filename) { //如果文件存在
		file, _ = os.OpenFile(filename, os.O_RDWR|os.O_APPEND, 0666) //打开文件不清空已追加方式打开，写入文件末尾
		fmt.Println("rfid文件存在")
	} else {
		file, _ = os.Create(filename) //创建文件
		fmt.Println("rfid文件不存在")
	}

	log.New(file, "", log.Llongfile)
	//默认会有log.Ldate | log.Ltime（日期 时间），这里重写为 日 时 文件名 设置log格式
	log.SetFlags(log.Ldate | log.Ltime) //2015/04/22 11:28:41  content

	//write log
	log.SetOutput(file)
	str := C.GoString(iotstr)
	log.Printf(str)
	file.Close()
}

/*==================================================================================
* 函 数 名： write_plate_write_sqlite_log
* 参    数：
* 功能描述:  写盘器定时读写数据库log
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/29
==================================================================================*/
//export write_plate_write_sqlite_log
func write_plate_write_sqlite_log(iotstr *C.char) {
	var file *os.File

	//以年月日为后缀创建CPU温度频率log文件
	year := time.Now().Format("2006")
	month := time.Now().Format("01")
	day := time.Now().Format("02")
	filename := fmt.Sprintf("/home/meican/logfiles/sqlite-%s-%s-%s.log", year, month, day)

	if checkFileIsExist(filename) { //如果文件存在
		file, _ = os.OpenFile(filename, os.O_RDWR|os.O_APPEND, 0666) //打开文件不清空已追加方式打开，写入文件末尾
		fmt.Println("sqlite文件存在")
	} else {
		file, _ = os.Create(filename) //创建文件
		fmt.Println("sqlite文件不存在")
	}

	log.New(file, "", log.Llongfile)
	//默认会有log.Ldate | log.Ltime（日期 时间），这里重写为 日 时 文件名 设置log格式
	log.SetFlags(log.Ldate | log.Ltime) //2015/04/22 11:28:41  content

	//write log
	log.SetOutput(file)
	str := C.GoString(iotstr)
	log.Printf(str)
	file.Close()
}

/*==================================================================================
* 函 数 名： write_plate_write_can_log
* 参    数：
* 功能描述:  写CAN信息log
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/09/08
==================================================================================*/
//export write_plate_write_can_log
func write_plate_write_can_log(iotstr *C.char) {
	var file *os.File

	//以年月日为后缀创建CPU温度频率log文件
	year := time.Now().Format("2006")
	month := time.Now().Format("01")
	day := time.Now().Format("02")
	filename := fmt.Sprintf("/home/meican/logfiles/can-%s-%s-%s.log", year, month, day)
	if checkFileIsExist(filename) { //如果文件存在
		file, _ = os.OpenFile(filename, os.O_RDWR|os.O_APPEND, 0666) //打开文件不清空已追加方式打开，写入文件末尾
		fmt.Println("can文件存在")
	} else {
		file, _ = os.Create(filename) //创建文件
		fmt.Println("can文件不存在")
	}

	log.New(file, "", log.Llongfile)
	//默认会有log.Ldate | log.Ltime（日期 时间），这里重写为 日 时 文件名
	//log.SetFlags(log.Ldate | log.Ltime | log.Lshortfile) //2015/04/22 11:28:41 test.go:29: content
	log.SetFlags(log.Ldate | log.Ltime) //2015/04/22 11:28:41  content

	//write log
	log.SetOutput(file)
	str := C.GoString(iotstr)
	log.Printf(str)
	file.Close()
}
