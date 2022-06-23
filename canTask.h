#include <stdio.h>
#include <sys/ioctl.h>
#include <arpa/inet.h>
#include <net/if.h>
#include <linux/socket.h>
#include <linux/can.h>
#include <linux/can/error.h>
#include <linux/can/raw.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <errno.h>
#include <time.h>


#define CAN_CHECK_START     0xAA//工厂检测命令包 包头
#define CAN_CHECK_END       0xA5//工厂检测命令包 包尾

//工厂检测指令
#define CHECK_SCREEN_CMD    0xB0//屏幕检测
#define CHECK_TOUCH_CMD     0xB1//检测触摸按键
#define CHECK_WIFI_CMD      0xB2//检测WiFi
#define CHECK_BLUE_CMD      0xB3//检测蓝牙
#define CHECK_BEEP_CMD      0xB4//检测蜂鸣器
#define CHECK_RFID_CMD      0xB5//检测读卡
#define CHECK_MOTOR_CMD     0xB6//检测电机
#define CHECK_VOICE_CMD     0xB7//检测语音播放
#define CHECK_REBOOT_CMD    0xB8//重启测试
#define CHECK_LED_CMD       0xB9//灯带测试
#define CHECK_CAN_CMD       0xBA//CAN communication test
#define GET_UUID_CMD        0xBB//获取UUID指令


typedef enum
{
	SCREEN_CHECK = 0xB0, //屏幕测试
    TOUCH_CHECK, //触摸测试
    WIFI_CHECK, // 触摸测试
    BLUE_CHECK, //蓝牙测试
    BEEP_CHECK, //蜂鸣器测试
    RFID_CHECK, //读盘测试
    MOTOR_CHECK, //电机测试
    VOICE_CHECK,  //语音测试
    LED_CHECK, //灯带测试
    CAN_CHECK, //CAN Test
	
}_factory_check;

//CAN数据
typedef union
{
	struct
	{
		uint8_t STA;//包头
		uint8_t data[200];//数据		
        uint16_t crc;//效验
        uint8_t END;//包尾
	}_Can_Msg_struct;
	uint8_t msg_buf[204];			
}_Can_Msg_Union;

void can_init(void);
void receive_can_msg_data_task(void);
void send_can_data(struct can_frame frdup);
int can_test(void);

/*==================================================================================
* 函 数 名： get_fatory_rfid_test_flag
* 参    数：
* 功能描述:  获取读卡测试标记
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/8/27
==================================================================================*/
bool get_fatory_rfid_test_flag(void);

/*==================================================================================
* 函 数 名： set_fatory_rfid_test_flag
* 参    数：
* 功能描述:  设置读卡测试标记
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/8/27
==================================================================================*/
void set_fatory_rfid_test_flag(bool status);