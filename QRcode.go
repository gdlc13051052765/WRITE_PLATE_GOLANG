package main

import "C"
import (
	"fmt"
	"image/png"
	"os"

	"github.com/boombuler/barcode"
	"github.com/boombuler/barcode/code128"
	qrcode "github.com/skip2/go-qrcode"
)

/*==================================================================================
* 函 数 名： make_mctid_qr_code
* 参    数：
* 功能描述:  生成写盘器 uuid 二维码图片
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/08/02
==================================================================================*/
func make_mctid_qr_code(qrstr string) {
	err := qrcode.WriteFile(qrstr, qrcode.Medium, 256, "/home/meican/mct_uuid.png")
	if err != nil {
		fmt.Println("write error")
	}
}

/*==================================================================================
* 函 数 名： make_mctid_barcode
* 参    数：
* 功能描述:  生成写盘器 sn 一维码图片
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/08/02
==================================================================================*/
//export make_mctid_barcode
func make_mctid_barcode(qrstr *C.char) {
	// 创建一个code128编码的 BarcodeIntCS
	str := C.GoString(qrstr)
	fmt.Printf("sn条形码 = %s\n", str)
	// cmd := exec.Command("/bin/sh", "-c", "rm -rf /home/meican/mct_sn.png")
	// if err := cmd.Start(); err != nil { // 运行命令
	// 	fmt.Println(err)
	// }
	// if err := cmd.Wait(); err != nil {
	// 	fmt.Println("wait:", err.Error())
	// }

	cs, _ := code128.Encode(str)
	// 创建一个要输出数据的文件
	file, _ := os.Create("/home/meican/mct_sn.png")
	defer file.Close()

	// 设置图片像素大小
	qrCode, _ := barcode.Scale(cs, 165, 30)
	// 将code128的条形码编码为png图片
	png.Encode(file, qrCode)
}
