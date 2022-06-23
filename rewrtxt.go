package main

import (
	"fmt"
	"os"

	// "io"
	"bufio"
	"strings"
)

/*==================================================================================
* 函 数 名： read_ip_from_txt
* 参    数： None
* 功能描述:  从配置文件里面读取ip地址信息
* 返 回 值： None
* 备    注： None
* 作    者： lc
* 创建时间： 2021/4/14
==================================================================================*/
func read_ip_from_txt() (ipstr _IpMessage) {

	fileName := "/home/meican/ipAddress.txt"
	file, err := os.OpenFile(fileName, os.O_RDWR, 0666)
	if err != nil {
		fmt.Println("Open file error!", err)
		return ipstr
	}
	defer file.Close()

	stat, err := file.Stat()
	if err != nil {
		panic(err)
	}

	var size = stat.Size()
	fmt.Println("file size=", size)
	//读取本机地址
	buf := bufio.NewReader(file)
	line, err := buf.ReadString('\n')
	line = strings.TrimSpace(line)
	line = line[8:len(line)]
	ResetValue(&ipstr.localip, line)
	//fmt.Println("localip =",ipstr.localip)
	//读取子网掩码
	line, _ = buf.ReadString('\n')
	line = strings.TrimSpace(line)
	line = line[5:len(line)]
	//fmt.Println(line)
	ResetValue(&ipstr.mask, line)
	//fmt.Println("mask =",ipstr.mask)
	//读取网关
	line, _ = buf.ReadString('\n')
	line = strings.TrimSpace(line)
	line = line[8:len(line)]
	ResetValue(&ipstr.gateway, line)
	//fmt.Println("gateway =",ipstr.gateway)
	//读取远端ip
	line, _ = buf.ReadString('\n')
	line = strings.TrimSpace(line)
	line = line[8:len(line)]
	ResetValue(&ipstr.routeip, line)
	//fmt.Println("routeip =",ipstr.routeip)
	//读取端口
	line, _ = buf.ReadString('\n')
	line = strings.TrimSpace(line)
	line = line[5:len(line)]
	ResetValue(&ipstr.port, line)
	//fmt.Println("port =",ipstr.port)
	//读取站点号
	line, _ = buf.ReadString('\n')
	line = strings.TrimSpace(line)
	line = line[12:len(line)]
	ResetValue(&ipstr.stationcode, line)
	//fmt.Println("stationcode =",ipstr.stationcode)
	//读取设备号
	line, _ = buf.ReadString('\n')
	line = strings.TrimSpace(line)
	line = line[9:len(line)]
	ResetValue(&ipstr.maincode, line)
	//fmt.Println("maincode =",ipstr.maincode)
	//读取脱机允许位
	line, _ = buf.ReadString('\n')
	line = strings.TrimSpace(line)
	line = line[6:len(line)]
	ResetValue(&ipstr.nonet, line)
	//fmt.Println("nonet =",ipstr.nonet)

	return ipstr
}
