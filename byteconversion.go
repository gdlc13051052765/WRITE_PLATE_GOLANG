package main

import (
	"bytes"
	"encoding/binary"
	"fmt"
)

//整形转换成字节
func IntToBytes(n int) []byte {
	x := int32(n)
	bytesBuffer := bytes.NewBuffer([]byte{})
	binary.Write(bytesBuffer, binary.BigEndian, x)
	return bytesBuffer.Bytes()
}

//字节转换成整形
func BytesToInt(b []byte) int {
	bytesBuffer := bytes.NewBuffer(b)
	var x int32
	binary.Read(bytesBuffer, binary.BigEndian, &x)
	return int(x)
}

//进制转换测试
func conversionTest() {
	//str := "ff68b4ff"
	money := int(1000)
	//str := strconv.FormatInt(money, 16)//10进制转HEX
	//fmt.Println("str = %d",str)
	//b, _ := hex.DecodeString(str)//字符串转16进制
	b := IntToBytes(money)
	fmt.Println(b)
	//encodedStr := hex.EncodeToString(str)//16进制转字符串
}

//字符串赋值
func ResetValue(s *string, newValue string) {
	sByte := []byte(*s)
	for i := 0; i < len(sByte); i++ {
		sByte[i] = ' '
	}
	*s = newValue
}

//byte 数组拷贝
func blockCopy(src []byte, srcOffset int, dst []byte, dstOffset int, count int) bool {
	srcLen := len(src)
	if srcOffset > srcLen || count > srcLen || srcOffset+count > srcLen {
		return false
	}
	dstLen := len(dst)
	if dstOffset > dstLen || count > dstLen || dstOffset+count > dstLen {
		return false
	}
	index := 0
	for i := srcOffset; i < srcOffset+count; i++ {
		dst[dstOffset+index] = src[srcOffset+index]
		index++
	}
	return true
}
