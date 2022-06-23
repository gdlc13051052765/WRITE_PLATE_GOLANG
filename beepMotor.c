#include "beepMotor.h"
#include <stdio.h>
#include <stdint.h>
#include <signal.h>
#include <sys/time.h>

#define BEEP_FREQUENCY  11 //蜂鸣器频率
static int beepCounter = 0;//蜂鸣器计数器
static int beepNumber = 0; //蜂鸣次数

static struct itimerval oldtv;
struct itimerval itv;

static void sig_alm_handler(int sig_num)
{
    if(sig_num = SIGALRM) beepCounter++;
    
    if(beepNumber) {
        if(beepCounter == 1) {
            system("echo 1 > /sys/class/gpio/gpio4/value");
        } 
        else if(beepCounter == BEEP_FREQUENCY) {
            system("echo 0 > /sys/class/gpio/gpio4/value");
        }        
    }

    if(beepCounter > BEEP_FREQUENCY*2) {
        beepCounter = 0;
        if(beepNumber) beepNumber--;     
    }
}

/*=======================================================================================
* 函 数 名： beep_motor_init
* 参    数： 
* 功能描述:  蜂鸣器电机GPIO初始化
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-09-22 
==========================================================================================*/
void beep_motor_init(void)
{
    //蜂鸣器
    system("echo 4 > /sys/class/gpio/unexport");
    system("echo 4 > /sys/class/gpio/export");
    system("echo out > /sys/class/gpio/gpio4/direction");
    //电机
    system("echo 8 > /sys/class/gpio/unexport");
    system("echo 8 > /sys/class/gpio/export");
    system("echo out > /sys/class/gpio/gpio8/direction");

    //蜂鸣器定时器
    //拦截定时器信号。
    signal(SIGALRM, sig_alm_handler);
    struct itimerval olditv;
    struct itimerval itv;
    itv.it_interval.tv_sec = 0; //定时周期为1秒钟。
    itv.it_interval.tv_usec = 10000;//10ms
    itv.it_value.tv_sec = 3; //定时器启动以后将在3秒又500微秒以后正式开始计时。
    itv.it_value.tv_usec = 500;
    setitimer(ITIMER_REAL, &itv, &olditv);
}

/*=======================================================================================
* 函 数 名： beep_on
* 参    数： 
* 功能描述:  蜂鸣器启动
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-09-22 
==========================================================================================*/
void beep_on(uint8_t num)
{
    beepCounter = 0;
    beepNumber = num;
}
