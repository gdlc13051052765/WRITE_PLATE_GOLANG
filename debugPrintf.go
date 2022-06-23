package main

import "fmt"

/*==================================================================================
* 函 数 名： debug_printf
* 参    数：
* 功能描述:  golang 调试打印接口，关闭打印时直接注释掉打印
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/5/13
==================================================================================*/
func debug_printf(format string, a ...interface{}) (n int, err error) {

	return fmt.Printf(format, a...)
	//return
}
