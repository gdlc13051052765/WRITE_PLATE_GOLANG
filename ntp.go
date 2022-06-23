package main

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"log"
	"net"
	"os/exec"
	"time"
)

const (
	UNIX_STA_TIMESTAMP = 2208988800
)

/**
NTP协议 http://www.ntp.org/documentation.html
@author mengdj@outlook.com
*/
type Ntp struct {
	//1:32bits
	Li        uint8 //2 bits
	Vn        uint8 //3 bits
	Mode      uint8 //3 bits
	Stratum   uint8
	Poll      uint8
	Precision uint8
	//2:
	RootDelay           int32
	RootDispersion      int32
	ReferenceIdentifier int32
	//64位时间戳
	ReferenceTimestamp uint64 //指示系统时钟最后一次校准的时间
	OriginateTimestamp uint64 //指示客户向服务器发起请求的时间
	ReceiveTimestamp   uint64 //指服务器收到客户请求的时间
	TransmitTimestamp  uint64 //指示服务器向客户发时间戳的时间
}

func NewNtp() (p *Ntp) {
	//其他参数通常都是服务器返回的
	p = &Ntp{Li: 0, Vn: 3, Mode: 3, Stratum: 0}
	return p
}

/**
构建NTP协议信息
*/
func (this *Ntp) GetBytes() []byte {
	//注意网络上使用的是大端字节排序
	buf := &bytes.Buffer{}
	head := (this.Li << 6) | (this.Vn << 3) | ((this.Mode << 5) >> 5)
	binary.Write(buf, binary.BigEndian, uint8(head))
	binary.Write(buf, binary.BigEndian, this.Stratum)
	binary.Write(buf, binary.BigEndian, this.Poll)
	binary.Write(buf, binary.BigEndian, this.Precision)
	//写入其他字节数据
	binary.Write(buf, binary.BigEndian, this.RootDelay)
	binary.Write(buf, binary.BigEndian, this.RootDispersion)
	binary.Write(buf, binary.BigEndian, this.ReferenceIdentifier)
	binary.Write(buf, binary.BigEndian, this.ReferenceTimestamp)
	binary.Write(buf, binary.BigEndian, this.OriginateTimestamp)
	binary.Write(buf, binary.BigEndian, this.ReceiveTimestamp)
	binary.Write(buf, binary.BigEndian, this.TransmitTimestamp)
	//[27 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
	return buf.Bytes()
}

func (this *Ntp) Parse(bf []byte, useUnixSec bool) {
	var (
		bit8  uint8
		bit32 int32
		bit64 uint64
		rb    *bytes.Reader
	)
	//貌似这binary.Read只能顺序读，不能跳着读，想要跳着读只能使用切片bf
	rb = bytes.NewReader(bf)
	binary.Read(rb, binary.BigEndian, &bit8)
	//向右偏移6位得到前两位LI即可
	this.Li = bit8 >> 6
	//向右偏移2位,向右偏移5位,得到前中间3位
	this.Vn = (bit8 << 2) >> 5
	//向左偏移5位，然后右偏移5位得到最后3位
	this.Mode = (bit8 << 5) >> 5
	binary.Read(rb, binary.BigEndian, &bit8)
	this.Stratum = bit8
	binary.Read(rb, binary.BigEndian, &bit8)
	this.Poll = bit8
	binary.Read(rb, binary.BigEndian, &bit8)
	this.Precision = bit8

	//32bits
	binary.Read(rb, binary.BigEndian, &bit32)
	this.RootDelay = bit32
	binary.Read(rb, binary.BigEndian, &bit32)
	this.RootDispersion = bit32
	binary.Read(rb, binary.BigEndian, &bit32)
	this.ReferenceIdentifier = bit32

	//以下几个字段都是64位时间戳(NTP都是64位的时间戳)
	binary.Read(rb, binary.BigEndian, &bit64)
	this.ReferenceTimestamp = bit64
	binary.Read(rb, binary.BigEndian, &bit64)
	this.OriginateTimestamp = bit64
	binary.Read(rb, binary.BigEndian, &bit64)
	this.ReceiveTimestamp = bit64
	binary.Read(rb, binary.BigEndian, &bit64)
	this.TransmitTimestamp = bit64
	//转换为unix时间戳,先左偏移32位拿到64位时间戳的整数部分，然后ntp的起始时间戳 1900年1月1日 0时0分0秒 2208988800
	if useUnixSec {
		this.ReferenceTimestamp = (this.ReceiveTimestamp >> 32) - UNIX_STA_TIMESTAMP
		if this.OriginateTimestamp > 0 {
			this.OriginateTimestamp = (this.OriginateTimestamp >> 32) - UNIX_STA_TIMESTAMP
		}
		this.ReceiveTimestamp = (this.ReceiveTimestamp >> 32) - UNIX_STA_TIMESTAMP
		this.TransmitTimestamp = (this.TransmitTimestamp >> 32) - UNIX_STA_TIMESTAMP
	}
}

/*==================================================================================
* 函 数 名： func ntp_time_calibration()
* 参    数：
* 功能描述:  NTP时间校准（阿里云服务器）
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/5/13
==================================================================================*/
func ntp_time_calibration() (err error) {
	var (
		ntp    *Ntp
		buffer []byte
		ret    int
	)
	//链接阿里云NTP服务器,NTP有很多免费服务器可以使用time.windows.com
	//connTimeout := 3 * time.Second //超时时间
	//conn, err := net.DialTimeout("udp", "time.windows.com:123", connTimeout)
	conn, err := net.Dial("udp", "ntp1.aliyun.com:123")
	defer func() {
		if err := recover(); err != nil {
			log.Println(err)
		}
		//conn.Close()
	}()
	if err != nil {
		return err
	}
	ntp = NewNtp()
	_, err1 := conn.Write(ntp.GetBytes())
	if err1 != nil {
		return err1
	}
	buffer = make([]byte, 1024)
	readTimeout := 2 * time.Second                          //超时时间
	err = conn.SetReadDeadline(time.Now().Add(readTimeout)) // timeout
	if err != nil {
		log.Println("setReadDeadline failed:", err)
	}
	ret, err = conn.Read(buffer)
	if err == nil {
		if ret > 0 {
			ntp.Parse(buffer, true)
			// fmt.Println(fmt.Sprintf(
			// 	"LI:%d\r\n版本:%d\r\n模式:%d\r\n精度:%d\r\n轮询:%d\r\n系统精度:%d\r\n延时:%ds\r\n最大误差:%d\r\n时钟表示:%d\r\n时间戳:%d %d %d %d\r\n",
			// 	ntp.Li,
			// 	ntp.Vn,
			// 	ntp.Mode,
			// 	ntp.Stratum,
			// 	ntp.Poll,
			// 	ntp.Precision,
			// 	ntp.RootDelay,
			// 	ntp.RootDispersion,
			// 	ntp.ReferenceIdentifier,
			// 	ntp.ReferenceTimestamp,
			// 	ntp.OriginateTimestamp,
			// 	ntp.ReceiveTimestamp,
			// 	ntp.TransmitTimestamp,
			// ))

			//调用linux命令行修改系统时间
			timeobj := time.Unix(int64(ntp.TransmitTimestamp+28800), 0)
			systime := timeobj.Format("2006-01-02 15:04:05")
			fmt.Printf("systime = %s \n", systime)
			cmdstr := fmt.Sprintf("date -s \"%s\"", systime)
			fmt.Printf("cmdstr = %s \n", cmdstr)
			cmd := exec.Command("/bin/sh", "-c", cmdstr)
			if err = cmd.Start(); err != nil {
				fmt.Println(err)
				return err
			}
			if err = cmd.Wait(); err != nil {
				fmt.Println(err)
				return err
			}
			//同步到硬件
			cmd = exec.Command("/bin/sh", "-c", "hwclock -w")
			if err = cmd.Start(); err != nil {
				fmt.Println(err)
				return err
			}
			if err = cmd.Wait(); err != nil {
				fmt.Println(err)
				return err
			}
			//time.Sleep(1 * time.Second)
			fmt.Println(time.Now().Format("2006-01-02 15:04:05"))
		} else {
		}
	}
	//清除超时设置
	if err := conn.SetReadDeadline(time.Time{}); err != nil {
		return err
	}
	return err
}
