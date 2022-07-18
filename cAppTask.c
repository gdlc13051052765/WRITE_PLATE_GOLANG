/*****************************************************************************************
 * 文件说明：
 * C线程任务管理
 * 为了减少CPU占有率，每个任务里面加入相应的延时
 *****************************************************************************************/

#include <stdio.h>  
#include <stdbool.h>  
#include <pthread.h>
#include <sys/time.h>
#include <string.h>

#include "rewrCardTask.h"
#include "sqliteTask.h"
#include "msgTask.h"
#include "debug_print.h"
#include "awsIotTask.h"
#include "canTask.h"


#define	RUN 	1
#define STOP	0

static pthread_t thread[10];  //两个线程
#define TASK_DELAY   1000 //线程间延时

static pthread_mutex_t mtx = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t cond = PTHREAD_COND_INITIALIZER;
static iotThreadStatus = STOP;


/*==================================================================================
* 函 数 名： write_plate_thread
* 参    数： Non
* 功能描述:  读写盘线程任务
* 返 回 值：
* 备    注： 调用C代码里面的读写盘任务函数
* 作    者： lc
* 创建时间： 2021/4/16
==================================================================================*/
static void *write_plate_thread(void *args) 
{
	while(1) 
	{
		nfc_write_plate_task();
		usleep(TASK_DELAY);
	}
}

/*==================================================================================
* 函 数 名： send_qt_msg_thread
* 参    数： Non
* 功能描述:  发送数据到qt进程通讯消息队列
* 返 回 值：
* 备    注： 调用C代码里面任务函数
* 作    者： lc
* 创建时间： 2021/4/16
==================================================================================*/
static void *send_qt_msg_thread(void *args) 
{
	uint32_t temp;

	while(1) 
	{
		temp = get_msg_task_delay();
		usleep(temp);
		send_qt_msg_data_task(); 
	}
}

/*==================================================================================
* 函 数 名： receive_qt_msg_thread
* 参    数： Non
* 功能描述:  接收qt信息进程通讯消息队列
* 返 回 值：
* 备    注： 调用C代码里面任务函数
* 作    者： lc
* 创建时间： 2021/4/16
==================================================================================*/
static void *receive_qt_msg_thread(void *args) 
{
	uint32_t temp;

	while(1) 
	{
		temp = get_msg_task_delay();
		usleep(temp);
		receive_qt_msg_data_task();
	}
}

/*==================================================================================
* 函 数 名： receive_can_msg_thread
* 参    数： Non
* 功能描述:  接收CAN信息任务处理
* 返 回 值：
* 备    注： 调用C代码里面任务函数
* 作    者： lc
* 创建时间： 2021/8/27
==================================================================================*/
static void *receive_can_msg_thread(void *args) 
{
	uint32_t temp;

	can_init();
	while(1) 
	{
		temp = get_msg_task_delay();
		usleep(temp);
		receive_can_msg_data_task();
	}
}

/*==================================================================================
* 函 数 名： aws_iot_monitor_thread
* 参    数： Non
* 功能描述:  监听AWS IOT 发过来的信息
* 返 回 值：
* 备    注： 调用C代码里面任务函数
* 作    者： lc
* 创建时间： 2021/4/16
==================================================================================*/
int iotStatus = 0;
static void *aws_iot_monitor_thread(void *args) 
{
	uint32_t temp;
	int status = -1;
	
	while(1) 
	{
		debug_print("iotStatus = %d \n",iotStatus);
    	// pthread_mutex_lock(&mtx);
		// while(!iotThreadStatus)
		// {
		// 	pthread_cond_wait(&cond, &mtx);
		// }
		// pthread_mutex_unlock(&mtx);
		
		switch(iotStatus)
		{
			case 0:
			status = sqlite_read_device_satus();//获取当前设备状态
			if(status >=1 &(get_net_status() == 1))//已经获取到AWS IOT证书并且获取到ntp时间
				iotStatus = 1;
			sleep(1);
			break;

			case 1://初始化AWS IOT 并连接AWS IOT 服务器
			status = write_plate_aws_iot_shadow_init();
			if(!status) {
				//iot初始化并连接成功
				iotStatus = 2;	
			}
			sleep(1);
			break;

			case 2:
			temp = get_msg_task_delay();
			usleep(temp);
			write_plate_aws_iot_shadow_task();
			break;
		}
	}
}

/*==================================================================================
* 函 数 名： hang_up_aws_iot_monitor_thread
* 参    数： Non
* 功能描述:  挂起aws iot线程
* 返 回 值：
* 备    注： 
* 作    者： lc
* 创建时间： 2021/5/6
==================================================================================*/
void hang_up_aws_iot_monitor_thread(void)
{
	if (iotThreadStatus == RUN) {
		pthread_mutex_lock(&mtx);
		iotThreadStatus = STOP;
		printf("thread stop!\n");
		pthread_mutex_unlock(&mtx);
	} else {
		printf("pthread pause already\n");
	}

}

/*==================================================================================
* 函 数 名： resume_aws_iot_monitor_thread
* 参    数： Non
* 功能描述:  恢复aws iot线程
* 返 回 值：
* 备    注： 
* 作    者： lc
* 创建时间： 2021/5/6
==================================================================================*/
void resume_aws_iot_monitor_thread(void)
{
	if (iotThreadStatus == STOP) {
		pthread_mutex_lock(&mtx);
		iotThreadStatus = RUN;
		pthread_cond_signal(&cond);
		printf("pthread run!\n");
		pthread_mutex_unlock(&mtx);
	} else {
		printf("pthread run already\n");
	}
}

/*==================================================================================
* 函 数 名： app_wrplate_create_thread
* 参    数： Non
* 功能描述:  创建多线程任务
* 返 回 值：
* 备    注： 
* 作    者： lc
* 创建时间： 2021/5/6
==================================================================================*/
void app_wrplate_create_thread(void)
{
	int temp;
	memset(&thread, 0, sizeof(thread));          
	pthread_mutex_init(&mtx,NULL);//初始化互斥锁
	pthread_cond_init(&cond, NULL);

	if((temp = pthread_create(&thread[1], NULL, write_plate_thread, NULL)) != 0)//读写盘线程任务
		debug_print("线程1创建失败\n");
	else
		debug_print("线程1被创建\n");
		
	if((temp = pthread_create(&thread[2], NULL, send_qt_msg_thread, NULL)) != 0)//发送数据到qt进程通讯消息队列
		debug_print("线程2创建失败\n");
	else
		debug_print("线程2被创建\n");

	if((temp = pthread_create(&thread[3], NULL, receive_qt_msg_thread, NULL)) != 0)//接收qt信息进程通讯消息队列
		debug_print("线程3创建失败\n");
	else
		debug_print("线程3被创建\n");	

	if((temp = pthread_create(&thread[4], NULL, aws_iot_monitor_thread, NULL)) != 0)//监听 aws iot 任务
		debug_print("线程4创建失败\n");
	else
		debug_print("线程4被创建\n");	
	resume_aws_iot_monitor_thread();

	if((temp = pthread_create(&thread[5], NULL, receive_can_msg_thread, NULL)) != 0)//监听 can 信息 任务
		debug_print("线程5创建失败\n");
	else
		debug_print("线程5被创建\n");	
}
