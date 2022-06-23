#include<stdio.h>
#include<stdlib.h>
#include<stdint.h>
#include<string.h>

//最大发送数据长度
#define MAX_LEN       512
//队列中最大的排队个数
#define MAX_CHANCE    50
//3s没收到回复重发
#define RETRY_TIME		3
//QT消息队列key id
#define SNDQTKEYID       88
#define RECQTKEYID       66

//QT---->>>golang 命令
#define WRPLATE_DATA_CMD          0x01//写盘信息命令
#define WRPLATE_STOP_CMD          0x02//停止写盘命令
#define WRPLATE_INIT_BIND_CMD     0x03//配网指令
#define WRPLATE_SITE_BIND_CMD     0x04//现场绑定食堂命令
#define WRPLATE_UNBIND_CMD        0x05//解绑命令
#define WRPLATE_OTA_REBOOT_CMD    0x06//ota golang重启
#define WRPLATE_REBOOT_CMD        0x07//golang重启

//golang---->>>QT 命令
#define WRPLATE_STAS_CMD         0xA1//写盘状态命令
#define WRPLATE_REMOVE_CMD       0xA2//标签离场命令
#define WRPLATE_NET_STATUS_CMD   0xA3//联网状态
#define WRPLATE_V2_ID_CMD        0xA4//发送id到QT用于二维码显示
#define WRPLATE_DEV_STATUS_CMD   0xA5//发送设备状态到QT
#define WRPLATE_MENU_STATUS_CMD  0xA6//发送菜单获取状态到QT
#define WRPLATE_OTA_UPDATE_CMD   0xA7//发送固件更新状态到QT

//工厂测试指令
#define WRPLATE_FACTORY_CHECK_CMD   0xFF//工厂检测指令

//消息队列信息结构体
typedef struct {
	int type;
	char mtext[MAX_LEN];
}mymesg_t,* p_mymesg_t;

//消息队列缓冲信息结构体
typedef struct {
	int len;
	char data[MAX_LEN];
}fifomesg_t,* p_fifomesg_t;

//消息队列FIFO结构体
typedef struct {
  fifomesg_t queue[MAX_CHANCE];
  char wp;
  char rd;
  char count;
}send_queue_t, * p_send_queue_t;

//通讯协议结构体
typedef struct{
  uint8_t datalen;//数据长度
  uint8_t cmd;//通讯命令
  uint8_t data[252];//数据体
  uint8_t crc8;//效验
}qtdata_t,* p_qtdata_t;

/*=======================================================================================
* 函 数 名： create_qt_msg
* 参    数： None
* 功能描述:  创建qt消息队列
* 返 回 值： 消息队列id
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int create_qt_msg(void);

/*=======================================================================================
* 函 数 名： del_msg
* 参    数： 消息队列ID
* 功能描述:  删除消息队列
* 返 回 值： 成功返回0
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int del_msg(int id);

/*=======================================================================================
* 函 数 名： send_qt_msg_data_task
* 参    数： 消息队列id，
* 功能描述:  循环检测是否有发送的数据
* 返 回 值： 成功返回0
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int send_qt_msg_data_task(void);

/*=======================================================================================
* 函 数 名： receive_qt_msg_data_task
* 参    数： 消息队列id，
* 功能描述:  接收qt消息队列信息
* 返 回 值： 成功返回0
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int receive_qt_msg_data_task(void);

/*=======================================================================================
* 函 数 名： qt_push_data_to_msg
* 参    数： None
* 功能描述:  创建qt消息队列
* 返 回 值： 消息队列id
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int qt_push_data_to_msg(qtdata_t sndDa_t);

/*=======================================================================================
* 函 数 名： get_stop_write_palte_status
* 参    数： 
* 功能描述:  返回是否停止写盘状态
* 返 回 值： 0==停止写盘;1==允许写盘
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int get_stop_write_palte_status(void);

/*=======================================================================================
* 函 数 名： get_msg_task_delay
* 参    数： 
* 功能描述:  返回消息队列任务的需要的延时时间
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int get_msg_task_delay();

/*=======================================================================================
* 函 数 名： msg_send_net_connect_status
* 参    数： 
* 功能描述:  status ==0 联网成功；status ==1 联网失败
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-08-03
==========================================================================================*/
void msg_send_net_connect_status(int status);

/*=======================================================================================
* 函 数 名： aws_send_change_status_to_qt
* 参    数： 
* 功能描述:  消息队列发送更改设备状态
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-30 
==========================================================================================*/
void aws_send_change_status_to_qt(int status);


/*=======================================================================================
* 函 数 名： set_stop_write_palte_status
* 参    数： 
* 功能描述:  设置停止写盘
* 返 回 值： 0==停止写盘;1==允许写盘
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int set_stop_write_palte_status(void);