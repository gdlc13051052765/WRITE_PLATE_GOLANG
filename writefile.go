package main

import (
	//缓存IO
	"fmt"
	"io" //io 工具包
	"os"
)

func check(e error) {
	if e != nil {
		panic(e)
	}
}

/**
 * 判断文件是否存在  存在返回 true 不存在返回false
 */
func checkFileIsExist(filename string) bool {
	var exist = true
	if _, err := os.Stat(filename); os.IsNotExist(err) {
		exist = false
	}
	return exist
}

/*==================================================================================
* 函 数 名： write_file_data
* 参    数： 请求参数:filename 文件路径； wireteString 写入文件内容
* 功能描述:  先清空文件再写入
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/4
==================================================================================*/
func write_file_data(filename string, wireteString string) error {

	var f *os.File
	var err1 error
	/***************************** 第一种方式: 使用 io.WriteString 写入文件 ***********************************************/
	if checkFileIsExist(filename) { //如果文件存在
		f, err1 = os.OpenFile(filename, os.O_RDWR|os.O_TRUNC|os.O_CREATE, 0766) //打开文件写文件清空覆盖
		fmt.Println("文件存在")
	} else {
		f, err1 = os.Create(filename) //创建文件
		fmt.Println("文件不存在")
	}
	check(err1)
	n, err1 := io.WriteString(f, wireteString) //写入文件(字符串)
	check(err1)
	fmt.Printf("写入 %d 个字节n", n)
	f.Close()
	return err1
}
