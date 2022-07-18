/*****************************************************************************************
 * 文件说明：
 * 消息队列用于跟QT进程相互通讯
 * 
 *****************************************************************************************/

#include<stdio.h>
#include<stdlib.h>
#include <sys/time.h>
#include<string.h>
#include<sys/msg.h>
#include<sys/ipc.h>
#include <time.h>

#include "msgTask.h"
#include "debug_print.h"
#include "bindTask.h"
#include "sqliteTask.h"
#include "canTask.h"

//跟QT通讯id
int qt_rec_msg_id;
int qt_snd_msg_id;
//QT消息队列数据
static send_queue_t	qtmsg_queue;
static last_ts =0;//上次发送的时间
static char stopWritePlateFlag = 0;//是否收到停止写盘命令 默认1==允许写盘

//消息队列任务延时
static uint32_t MSGTASKDELAY = 500;//500ms

//私有函数
static int send_msg_data(int id ,char *senddata,int sendlen);

//打印当前时间
static void print_current_time(void)
{
  struct timeval    tv;  
  struct timezone tz;  
  struct tm  *p;  

  gettimeofday(&tv, &tz);  
  // printf("tv_sec:%ld\n",tv.tv_sec);  
  // printf("tv_usec:%ld\n",tv.tv_usec);  
  // printf("tz_minuteswest:%d\n",tz.tz_minuteswest);  
  // printf("tz_dsttime:%d\n",tz.tz_dsttime);  

  p = localtime(&tv.tv_sec);  
  printf("%d /%d /%d %d :%d :%d.%3ld\n", 1900+p->tm_year, 1+p->tm_mon, p->tm_mday, p->tm_hour, p->tm_min, p->tm_sec, tv.tv_usec);  
}

//异或效验
static unsigned char Cal_Crc(unsigned char *Data, unsigned char Len)
{    
  unsigned char Crc = 0, i = 0;    
  for(i=0; i<Len; i++)    
  {        
    Crc = Crc ^ Data[i];    
  }    
  return Crc;
}

//消息队列填充初始化
static void msg_queue_init(p_send_queue_t p_queue_buff)
{
  memset(p_queue_buff, 0, sizeof(p_send_queue_t));
}
//队列里面排队个数
static int msg_queue_num(p_send_queue_t p_queue_buff)
{
  return p_queue_buff->count;
}

volatile unsigned char queue_mutex=0;
//填充队列信息
static void msg_queue_push(p_send_queue_t p_queue_buff, fifomesg_t *data)
{
  if(queue_mutex == 0)
  {
    queue_mutex = 1;
    if (p_queue_buff->count >= MAX_CHANCE)
    {
      memset(&p_queue_buff->queue[p_queue_buff->rd], 0, sizeof(fifomesg_t));
      p_queue_buff->rd = (p_queue_buff->rd + 1) % MAX_CHANCE;
      //log_printf("Delete the oldest member \r\n");
    } else {
        p_queue_buff->count++;
        //debug_print("p_queue_buff.count = %d \n",p_queue_buff.count);
    }
   // debug_print("sizeof(fifomesg_t) = %d \n",sizeof(fifomesg_t));
    memcpy(&p_queue_buff->queue[p_queue_buff->wp], data, sizeof(fifomesg_t));
    p_queue_buff->wp++;
    if(p_queue_buff->wp >= MAX_CHANCE)
      p_queue_buff->wp = 0;
    queue_mutex = 0;
  }
  else
  {
      //log_printf("queue is locked by others.\r\n");
  }
}
//移除队列信息
static void msg_queue_pop(p_send_queue_t p_queue_buff, uint8_t cmd)
{
  debug_print("msg_queue_pop quene = %02x cmd = %02x \n", p_queue_buff->queue[p_queue_buff->rd].data[1], cmd);
  if (p_queue_buff->queue[p_queue_buff->rd].data[1] == cmd)
  {
    memset(&p_queue_buff->queue[p_queue_buff->rd], 0, sizeof(fifomesg_t));
    if (p_queue_buff->count)
      p_queue_buff->count--;
    p_queue_buff->rd++;
    if (p_queue_buff->rd >= MAX_CHANCE)
      p_queue_buff->rd = 0;
  }
}

uint8_t send_num_bak = 0;
static uint8_t msg_queue_ready(void)
{
  unsigned int num;
  unsigned int ts;
  struct timeval tv;

  //获取当前系统时间
  gettimeofday(&tv, NULL);
  ts = tv.tv_sec; //两次发送间隔&& (ts - last_ts > 3)
  //debug_print("ts = %d \n",ts);

  num = msg_queue_num(&qtmsg_queue);
  //debug_print("queue num = %d \n",num);

  if(send_num_bak !=num)
  {
    send_num_bak = num;
    return 1;
  }
  if (num > 0 && (ts - last_ts > RETRY_TIME))//间隔RETRY_TIME 没有收到安卓回复重发指令
  {
    return 1;
  }
  else
  {
    return 0;
  }
}

static void msg_queue_send(p_send_queue_t p_queue_buff)
{
  fifomesg_t c_msg;
  struct timeval tv;

  //获取当前系统时间
  gettimeofday(&tv, NULL);
  last_ts = tv.tv_sec;//记录发送时间

	memcpy(&c_msg, &p_queue_buff->queue[p_queue_buff->rd], sizeof(fifomesg_t));
  send_msg_data(qt_snd_msg_id, c_msg.data,c_msg.len);
  //debug_print("msg send type = %02X, data = %s \n",c_msg.type,c_msg.mtext);
}

/*=======================================================================================
* 函 数 名： qt_push_data_to_msg
* 参    数： None
* 功能描述:  创建qt消息队列
* 返 回 值： 消息队列id
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int qt_push_data_to_msg(qtdata_t sndDa_t)
{
  char senddata[200];
  fifomesg_t fifomsg;

  fifomsg.data[0] = sndDa_t.datalen;//数据长度
  fifomsg.data[1] = sndDa_t.cmd;//命令
  memcpy(fifomsg.data+2,sndDa_t.data,sndDa_t.datalen-2);//数据体

  sndDa_t.crc8 = Cal_Crc(fifomsg.data,sndDa_t.datalen);
  fifomsg.data[sndDa_t.datalen] = sndDa_t.crc8;//效验

  fifomsg.len = sndDa_t.datalen+1;
  if(sndDa_t.datalen)
  {
    msg_queue_push(&qtmsg_queue, &fifomsg);
    //debug_print("fifomsg cmd = %02x \n",fifomsg.data[1]);
  }   
}

/*=======================================================================================
* 函 数 名： create_qt_msg
* 参    数： None
* 功能描述:  创建qt消息队列
* 返 回 值： 消息队列id
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int create_qt_msg(void)
{
  int id = -1;
  qtdata_t sndMsg;

  //接收消息队列从QTKEY
  key_t qt_msg_key = ftok("/tmp",RECQTKEYID);
	id = msgget(qt_msg_key,IPC_CREAT | 0666);
	if(id == -1)
	{
		printf("create qt msg error \n");
		return -1;
	}
  
  qt_rec_msg_id = id;
  debug_print("qt msg id =%d \n",qt_rec_msg_id);
  msg_queue_init(&qtmsg_queue);

  //发送消息队列到QT
  qt_msg_key = ftok("/tmp",SNDQTKEYID);
	qt_snd_msg_id = msgget(qt_msg_key,IPC_CREAT | 0666);
	if(id == -1)
	{
		printf("create qt msg error \n");
		return -1;
	}
  debug_print("qt msg id =%d \n",qt_snd_msg_id);
  /**************消息队列测试*******************/
  // sndMsg.datalen = 3;
  // sndMsg.cmd = 0xA1;
  // sndMsg.data[0] = 0;
  // sndMsg.crc8 = 0x33;
  // qt_push_data_to_msg(sndMsg);
  // sndMsg.datalen = 6;
  // sndMsg.cmd = 0x01;
  // memcpy(sndMsg.data,"\x43\x04\x00\x00",4);
  // sndMsg.crc8 = 0x44;
  // qt_push_data_to_msg(sndMsg);
  /***********************************/
  return id;
}

/*=======================================================================================
* 函 数 名： send_msg_data
* 参    数： None
* 功能描述:  消息队列int id ,发送数据int type(命令),char *senddata(数据),int sendlen(发送数据长度)
* 返 回 值： 发送成功返回0
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
static int send_msg_data(int id, char *senddata, int sendlen)
{
  uint8_t i =0;
  mymesg_t ckxmsg;
  ckxmsg.type = SNDQTKEYID;

  if(!sendlen)
  {
    return -1;
  }
  memcpy(ckxmsg.mtext,senddata,sendlen);

 // debug_print("send data len =%d \n",sendlen);
  debug_print("send data = ");
  for(i=0;i<sendlen;i++)
    debug_print("%02x ",ckxmsg.mtext[i]);
  debug_print("\n");

  debug_print("send time = ");
  print_current_time();//打印当前时间
  if(msgsnd(id,(void *)&ckxmsg,sendlen+4,0) < 0)
  {
    printf("send msg error \n");
    return -1;
  }
  return 0;
}

/*=======================================================================================
* 函 数 名： del_msg
* 参    数： None
* 功能描述:  删除qt消息队列
* 返 回 值： 成功返回0
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int del_msg(int id)
{
  if(msgctl(id,IPC_RMID,NULL) < 0)
	{
		printf("del qt msg error \n");
		return -1;
	}
  return 0;
}

/*=======================================================================================
* 函 数 名： send_qt_msg_data_task
* 参    数： 消息队列id，
* 功能描述:  循环检测是否有发送的数据
* 返 回 值： 成功返回0
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int send_qt_msg_data_task(void)
{
	//检查是否符合发送条件
	if(msg_queue_ready())
	{
    MSGTASKDELAY = 500;//队列任务延时设置成500us
		//发送数据
		msg_queue_send(&qtmsg_queue);
	}
}

/*=======================================================================================
* 函 数 名： send_data_to_qt_direct
* 参    数： 
* 功能描述:  直接发送数据到QT无需队列等待
* 返 回 值： 成功返回0
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int send_data_to_qt_direct(qtdata_t data_t)
{
  uint8_t pdata[200];

  pdata[0] = data_t.datalen;
  pdata[1] = data_t.cmd;
  memcpy(pdata+2,data_t.data,data_t.datalen-2);
  data_t.crc8 = Cal_Crc(pdata,data_t.datalen);
  pdata[data_t.datalen] = data_t.crc8;

  send_msg_data(qt_snd_msg_id,pdata, data_t.datalen+1);
}

/*=======================================================================================
* 函 数 名： get_stop_write_palte_status
* 参    数： 
* 功能描述:  返回是否停止写盘状态
* 返 回 值： 0==停止写盘;1==允许写盘
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int get_stop_write_palte_status(void)
{
  return stopWritePlateFlag;
}

/*=======================================================================================
* 函 数 名： set_stop_write_palte_status
* 参    数： 
* 功能描述:  设置停止写盘
* 返 回 值： 0==停止写盘;1==允许写盘
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int set_stop_write_palte_status(void)
{
  stopWritePlateFlag = 0;
}
/*=======================================================================================
* 函 数 名： receive_qt_msg_data_task
* 参    数： 消息队列id，
* 功能描述:  接收qt消息队列信息
* 返 回 值： 成功返回0
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int receive_qt_msg_data_task(void)
{
  mymesg_t ckxmsg; 
  int rec_len = 0,i=0;
  int food_id = 0;
  char context[100] = "西红柿鸡蛋";
  qtdata_t mSndMsg;
  struct can_frame frdup;

  rec_len = msgrcv(qt_rec_msg_id, (void *)&ckxmsg, 512, RECQTKEYID, 0);
  if(rec_len < 0) {
    debug_print("receive msg error \n");
    return -1;
  } else {
   // debug_print("ckxmsg.type = %02x \n",ckxmsg.type);
    debug_print("rece time = ");
    print_current_time();
    debug_print("rec data = ");
    for(i=0;i<ckxmsg.mtext[0]+1;i++)
      debug_print("%02x ", ckxmsg.mtext[i]);
    debug_print("\n");

    MSGTASKDELAY = 10000;//队列任务延时设置成10ms
    switch(ckxmsg.mtext[1])
    {
      /**************QT 发送指令到 golang**************************/
      case WRPLATE_DATA_CMD ://写盘信息命令 0x01
        memcpy(&food_id,ckxmsg.mtext+2,4);
        if(food_id==0)
        {
          return;
        }
        debug_print("food_id = %d \n",food_id);
        sqlite_write_food_menu_db(context,food_id,0);
        mSndMsg.datalen = 3;
        mSndMsg.cmd = WRPLATE_DATA_CMD;
        mSndMsg.data[0] = 0;//
        send_data_to_qt_direct(mSndMsg);//直接发送应答回复到QT
        stopWritePlateFlag = 1;//允许写盘
      break;
      case WRPLATE_STOP_CMD ://停止写盘 0x02
        debug_print("stop write plate cmd \n");
        mSndMsg.datalen = 3;
        mSndMsg.cmd = WRPLATE_STOP_CMD;
        mSndMsg.data[0] = 0;//
        send_data_to_qt_direct(mSndMsg);//直接发送应答回复到QT

        stopWritePlateFlag = 0;//停止写盘
      break;
      case WRPLATE_INIT_BIND_CMD://现场绑定命令blue scan获取wifi账号跟密码
      // get_wifi_ssid_passed();
        mSndMsg.datalen = 2;
        mSndMsg.cmd = WRPLATE_INIT_BIND_CMD;
        write_plate_set_config_wifi(1);
        send_data_to_qt_direct(mSndMsg);//配网指令应答
        debug_print("golang 配网 \n");
        
        write_plate_set_blue_scan();
        hang_up_aws_iot_monitor_thread();//挂起AWS IOT线程
      break;
      case WRPLATE_UNBIND_CMD://解除绑定
        //修改配置数据设备状态为本地解绑完成上传解绑状态到 IOT （4）
        sqlite_update_dev_status_config_db(C_LOCAL_UNBIND_STATUS);
        write_plate_updata_dev_status(C_LOCAL_UNBIND_STATUS);
        //删除菜单数据库
        //system("find -name \"menu*\" | xargs rm -rfv");
        system("rm -rf /home/meican/menudb");
        sleep(1);
        system("mkdir /home/meican/menudb");
        sleep(1);
        mSndMsg.datalen = 3;
        mSndMsg.cmd = WRPLATE_UNBIND_CMD;
        mSndMsg.data[0] = 0;//
        send_data_to_qt_direct(mSndMsg);//直接发送应答回复到QT
      break;
      case WRPLATE_OTA_REBOOT_CMD://ota golang重启
        //reboot_golang();
        system("/home/meican/otaReboot.sh");
      break;
      case WRPLATE_REBOOT_CMD://golang重启
        debug_print("golang重启");
        //system("hciconfig hci0 down");//停止蓝牙搜索
        sleep(1);
        //system("/home/meican/rebootgolang.sh");
        
      break;

      /**************QT 应答 golang 发送过去的命令******************************/
      case WRPLATE_STAS_CMD ://QT写盘状态回复命令 0xA1
        debug_print("write plate status response \n");
        msg_queue_pop(&qtmsg_queue,WRPLATE_STAS_CMD);//把发送写盘状态移除发送队列
      break;
      case WRPLATE_REMOVE_CMD ://QT卡片离场回复命令 0xA2
        debug_print("label remove status response \n");
        msg_queue_pop(&qtmsg_queue,WRPLATE_REMOVE_CMD);//把移除发送队列
      break;

      /***************工厂硬件检测指令****************************************/
      case WRPLATE_FACTORY_CHECK_CMD://
        system("echo 0 > /sys/class/gpio/gpio4/value");
        system("echo 0 > /sys/class/gpio/gpio8/value");
        system("echo 0 > /sys/class/gpio/gpio9/value");
        
        set_fatory_rfid_test_flag(false);//停止读卡测试
        if(ckxmsg.mtext[3] == 0) {//检测成功
          //can 发送数据
          frdup.can_dlc = 5;
          frdup.data[0] = 0xAA;
          frdup.data[1] = 0x30;
          frdup.data[2] = 0x14;
          frdup.data[3] = 0x00;
          frdup.data[4] = 0xA5;
          send_can_data(frdup); 
        } else {
          //can 发送数据
          frdup.can_dlc = 5;
          frdup.data[0] = 0xAA;
          frdup.data[1] = 0x31;
          frdup.data[2] = 0xD4;
          frdup.data[3] = 0xC1;
          frdup.data[4] = 0xA5;
          send_can_data(frdup); 
        }
      break;
    }
  }
}

/*=======================================================================================
* 函 数 名： msg_send_net_connect_status
* 参    数： 
* 功能描述:  status == 0 联网成功；status == 1 联网失败
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-08-03
==========================================================================================*/
void msg_send_net_connect_status(int status)
{
 //发送联网指令到QT
  qtdata_t mSndMsg;

  mSndMsg.datalen = 3;
  mSndMsg.cmd = 0xA3;
  mSndMsg.data[0] = status;
  send_data_to_qt_direct(mSndMsg);//发送设备状态到QT
}

/*=======================================================================================
* 函 数 名： get_msg_task_delay
* 参    数： 
* 功能描述:  返回消息队列任务的需要的延时时间
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-25 
==========================================================================================*/
int get_msg_task_delay()
{
  return MSGTASKDELAY;
}
