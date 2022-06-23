package main

import (
	"bufio"
	"bytes"
	"fmt"
	"io"
	"net"
	"os/exec"
)

/*==================================================================================
* 函 数 名： func get_net_mac_message()
* 参    数：
* 功能描述:  获取mac地址
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/5/13
==================================================================================*/
//将[]uinit8转换为string：
func B2S(bs []int8) string {
	ba := []byte{}
	for _, b := range bs {
		ba = append(ba, byte(b))
	}
	return string(ba)
}

//命令行读取ifconfig 信息
func RunCMD() {
	cmd0 := exec.Command("ifconfig")
	stdout0, err := cmd0.StdoutPipe() // 获取命令输出内容
	if err != nil {
		fmt.Println(err)
		return
	}
	if err := cmd0.Start(); err != nil { //开始执行命令
		fmt.Println(err)
		return
	}

	useBufferIO := false
	if !useBufferIO {
		var outputBuf0 bytes.Buffer
		for {
			tempoutput := make([]byte, 2048)
			n, err := stdout0.Read(tempoutput)
			if err != nil {
				if err == io.EOF { //读取到内容的最后位置
					break
				} else {
					fmt.Println(err)
					return
				}
			}
			if n > 0 {
				outputBuf0.Write(tempoutput[:n])
			}
		}
		fmt.Println(outputBuf0.String())
	} else {
		outputbuf0 := bufio.NewReader(stdout0)
		touput0, _, err := outputbuf0.ReadLine()
		if err != nil {
			return
		}
		fmt.Println(string(touput0))
	}
}

func get_net_mac_message() {
	interfaces, err := net.Interfaces()

	if err != nil {
		panic("Poor soul, here is what you got: " + err.Error())

	}
	for _, inter := range interfaces {
		//fmt.Println(inter.Name, inter.HardwareAddr)
		fmt.Printf("name = %t", inter.Name)
		fmt.Printf("name = %v", inter.Name)
		fmt.Printf("HardwareAddr = %t", inter.HardwareAddr)
		fmt.Printf("HardwareAddr = %v\n", inter.HardwareAddr)

		str, _ := net.ParseMAC(string(inter.HardwareAddr))
		fmt.Printf("mac 地址 = %s\n", str)
	}

	//RunCMD()
}
