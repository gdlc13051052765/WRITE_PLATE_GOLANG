
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

void app_wrplate_create_thread(void);

/*==================================================================================
* 函 数 名： hang_up_aws_iot_monitor_thread
* 参    数： Non
* 功能描述:  挂起aws iot线程
* 返 回 值：
* 备    注： 
* 作    者： lc
* 创建时间： 2021/5/6
==================================================================================*/
void hang_up_aws_iot_monitor_thread(void);

/*==================================================================================
* 函 数 名： rescover_aws_iot_monitor_thread
* 参    数： Non
* 功能描述:  恢复aws iot线程
* 返 回 值：
* 备    注： 
* 作    者： lc
* 创建时间： 2021/5/6
==================================================================================*/
void resume_aws_iot_monitor_thread(void);