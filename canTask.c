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
#include <string.h>
#include <errno.h>
#include <time.h>
#include "canTask.h"
#include "debug_print.h"
#include "crc.h"
#include "msgTask.h"
#include "sqliteTask.h"

#ifndef AF_CAN
#define AF_CAN 29
#endif
#ifndef PF_CAN
#define PF_CAN AF_CAN
#endif

static int fileFd;
static int master = 0;
static bool rfidTestFlag = false;//工厂读卡测试标记


//16进制字符串转为16进制
void StrToHex(uint8_t* pbDest, uint8_t* pbSrc, uint8_t nLen)
{
	uint8_t h1,h2;
	uint8_t s1,s2;
	uint8_t i;

	for (i = 0; i < nLen; i++)
	{
		h1 = pbSrc[2*i];
		h2 = pbSrc[2*i+1];

		s1 = toupper(h1) - 0x30;
		if (s1 > 9)
			s1 -= 7;

		s2 = toupper(h2) - 0x30;
		if (s2 > 9)
			s2 -= 7;

		pbDest[i] = s1*16 + s2;
	}
}

//16进制转为16进制字符串
void HexToStr(char *pbDest, char *pbSrc, int nlen)
{
	char ddl,ddh;
	int i;

	for(i=0; i<nlen; i++)
	{
		ddh = 48 +pbSrc[i] / 16;
		ddl = 48 +pbSrc[i] % 16;
		if(ddh>57) ddh = ddh+7;
		if(ddl>57) ddl = ddl+7;
		pbDest[i*2] = ddh;
		pbDest[i*2+1] =ddl;
	}
	pbDest[nlen*2] = '\0';
}

static void print_frame(struct can_frame *fr)
{
	int i;

	debug_print("%08x\n", fr->can_id & CAN_EFF_MASK);
	//printf("%08x\n", fr->can_id);
	//debug_print("dlc = %d\n", fr->can_dlc);
	debug_print("data = ");
	for (i = 0; i < fr->can_dlc; i++)
		debug_print("%02x ", fr->data[i]);
	debug_print("\n");
}

#define errout(_s)	fprintf(stderr, "error class: %s\n", (_s))
#define errcode(_d) fprintf(stderr, "error code: %02x\n", (_d))

static void handle_err_frame(const struct can_frame *fr)
{
	if (fr->can_id & CAN_ERR_TX_TIMEOUT) {
		errout("CAN_ERR_TX_TIMEOUT");
	}
	if (fr->can_id & CAN_ERR_LOSTARB) {
		errout("CAN_ERR_LOSTARB");
		errcode(fr->data[0]);
	}
	if (fr->can_id & CAN_ERR_CRTL) {
		errout("CAN_ERR_CRTL");
		errcode(fr->data[1]);
	}
	if (fr->can_id & CAN_ERR_PROT) {
		errout("CAN_ERR_PROT");
		errcode(fr->data[2]);
		errcode(fr->data[3]);
	}
	if (fr->can_id & CAN_ERR_TRX) {
		errout("CAN_ERR_TRX");
		errcode(fr->data[4]);
	}
	if (fr->can_id & CAN_ERR_ACK) {
		errout("CAN_ERR_ACK");
	}
	if (fr->can_id & CAN_ERR_BUSOFF) {
		errout("CAN_ERR_BUSOFF");
	}
	if (fr->can_id & CAN_ERR_BUSERROR) {
		errout("CAN_ERR_BUSERROR");
	}
	if (fr->can_id & CAN_ERR_RESTARTED) {
		errout("CAN_ERR_RESTARTED");
	}
}
#define myerr(str)	fprintf(stderr, "%s, %s, %d: %s\n", __FILE__, __func__, __LINE__, str)

static int test_can_rw(int fd, int master)
{
	int ret;
	struct can_frame frdup;
	//struct timeval tv;
	fd_set rset;

	while (1) 
	{
		//tv.tv_sec = 1;
		//tv.tv_usec = 0;
		FD_ZERO(&rset);
		FD_SET(fd, &rset);
		/*ret = select(fd+1, &rset, NULL, NULL, NULL);
		if (ret == 0) {
			myerr("select time out");
			return -1;
		}*/
		printf("------------------------ \n");
		ret = read(fd, &frdup, sizeof(frdup));
		if (ret < sizeof(frdup)) {
			myerr("read failed");
			return -1;
		}
		if (frdup.can_id & CAN_ERR_FLAG) {/* 出错设备错误 */
			handle_err_frame(&frdup);
			myerr("CAN device error");
			continue;
		}
		print_frame(&frdup);
		ret = write(fd, &frdup, sizeof(frdup));
		if (ret < 0) {
			myerr("write failed");
			return -1;
		}
	}
	return 0;
}

/*==================================================================================
* 函 数 名： factory_check_data_analysis
* 参    数：
* 功能描述:  工厂检测数据分析
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/08/31
==================================================================================*/
static uint8_t can_rec_status = 0;//CAN数据接收状态
static uint8_t can_rec_buf[255] = {0};//CAN接收数据缓存
static uint8_t can_rec_data_len = 0;//can接收数据长度
static _Can_Msg_Union p_can_union;//can信息结构体
static char blue_test_name[100] = {0};//需要检测的蓝牙名字
static int mct_dev_bak = 0;//写盘器初始状态备份
static int write_wifi_msg_file(char *sf)
{
    FILE * pFile;
  
    //pFile = fopen ("wifi.txt", "w");
	pFile = fopen ("/etc/wpa_supplicant.conf", "w");
    fwrite (sf , sizeof(char), strlen(sf), pFile);
    fclose (pFile);
	printf("创建成功!\n");
    return 0;
}

/*==================================================================================
* 函 数 名： _System
* 参    数：
* 功能描述:  回读命令行数据
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/09/09
==================================================================================*/
static int _System(const char *cmd, char *pRetMsg, int msg_len)
{
	FILE * fp;
	char * p = NULL;
	int res = -1;
	if (cmd == NULL || pRetMsg == NULL || msg_len < 0) {
		printf("Param Error!\n");
		return -1;
	}
	if ((fp = popen(cmd, "r") ) == NULL) {
		printf("Popen Error!\n");
		return -2;
	} else {
		memset(pRetMsg, 0, msg_len);
		//get lastest result
		while(fgets(pRetMsg, msg_len, fp) != NULL)
		{
			printf("Msg:%s", pRetMsg); //print all info
			// if(strstr(pRetMsg, blue_test_name)) {//是否包含需要搜索的蓝牙名字
			// 	printf("蓝牙检测成功 \n");
			// 	return 0;
			// }
			if(strlen(pRetMsg)){
				printf("蓝牙检测成功 \n");
				return 0;
			}
		}
		if ((res = pclose(fp)) == -1) {
			printf("close popenerror!\n");
			return -3;
		}
		pRetMsg[strlen(pRetMsg)-1] = '\0';
		return -1;
	}
}

#define blue_detect_counter   5
/*==================================================================================
* 函 数 名： factory_check_data_analysis
* 参    数：
* 功能描述:  工厂硬件测试CAN命令解析
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/09/09
==================================================================================*/
static char devSn[100]={};//设备SN码
static char code[100]={};//设备sn code码
static void factory_check_data_analysis(struct can_frame frdup)
{
	int crc_result, i,status;
	uint8_t tempbuf[255] = {0};
	uint8_t ssid[200] = {0};
	uint8_t psk[200] = {0};
	uint8_t logbuf[500] = {0};
	qtdata_t mSndMsg;
	static C_DevMsgSt devMsg;//写盘器配置信息
	char sendbuf[8];

	memset(tempbuf,0,255);
	memset(ssid,0,255);
	memset(psk,0,255);
	switch(can_rec_status)
	{
		case 0:
			can_rec_data_len = 0;
			memset(can_rec_buf,0,255);
			if(frdup.data[0] == CAN_CHECK_START) {
				can_rec_status = 1;
				can_rec_data_len = frdup.can_dlc - 1;
				memcpy(can_rec_buf, frdup.data+1, frdup.can_dlc-1);	
			}
		break;

		case 1://
			memcpy(can_rec_buf+can_rec_data_len, frdup.data, frdup.can_dlc);
			can_rec_data_len += frdup.can_dlc;
		break;
	}
	crc_result = crc16_calc(can_rec_buf, can_rec_data_len-3);
    printf("crc16test result = %2X %2X  %d\n", crc_result >> 8, crc_result & 0x00ff, crc_result);
	//检测到包尾
	if(can_rec_buf[can_rec_data_len -1] == CAN_CHECK_END) {
		printf("包围效验 = %d\n",can_rec_buf[can_rec_data_len-3]*256 + can_rec_buf[can_rec_data_len-2]);
		if(crc_result == can_rec_buf[can_rec_data_len-3]*256 + can_rec_buf[can_rec_data_len-2]) {
			printf("效验成功\r\n");
			can_rec_status = 0;
			memcpy(p_can_union.msg_buf+1, can_rec_buf, can_rec_data_len);
			sprintf(logbuf, "%s", "效验成功");
			write_plate_write_can_log(logbuf);
		} else {

		}
	} else {
		return;
	}

	debug_print("can 解析数据 = ");
    for (i = 0; i < can_rec_data_len; i++)
		debug_print("%02x ", p_can_union.msg_buf[i+1]);
    debug_print("\n");

	//16进制字符串转为16进制
	HexToStr(logbuf, p_can_union.msg_buf,can_rec_data_len);
	write_plate_write_can_log(logbuf);

	switch (p_can_union._Can_Msg_struct.data[0] ) 
	{
		case CHECK_SCREEN_CMD://屏幕检测
			mSndMsg.datalen = 4;
			mSndMsg.cmd = WRPLATE_FACTORY_CHECK_CMD;
			mSndMsg.data[0] = SCREEN_CHECK;//
			mSndMsg.data[1] = 0;//
			send_data_to_qt_direct(mSndMsg);//直接发送应答回复到Q
			sprintf(logbuf, "%s", "屏幕检测");
		break;

		case CHECK_TOUCH_CMD://检测触摸按键
			mSndMsg.datalen = 4;
			mSndMsg.cmd = WRPLATE_FACTORY_CHECK_CMD;
			mSndMsg.data[0] = TOUCH_CHECK;//
			mSndMsg.data[1] = 0;//
			send_data_to_qt_direct(mSndMsg);//直接发送应答回复到Q
			sprintf(logbuf, "%s", "触摸检测");
		break;

		case CHECK_WIFI_CMD://检测WiFi
			//sleep(5);
			printf("golang wifi 测试\n\n\n");
			mSndMsg.datalen = 4;
			mSndMsg.cmd = WRPLATE_FACTORY_CHECK_CMD;
			mSndMsg.data[0] = WIFI_CHECK;//
			mSndMsg.data[1] = 0;//
			send_data_to_qt_direct(mSndMsg);//直接发送应答回复到
			memcpy(tempbuf, p_can_union._Can_Msg_struct.data+2, p_can_union._Can_Msg_struct.data[1]);
			for(i=0;i<p_can_union._Can_Msg_struct.data[1];i++)
			{
				if(p_can_union._Can_Msg_struct.data[i+2] == 0x3B) {
					memcpy(psk, &p_can_union._Can_Msg_struct.data[i]+3, p_can_union._Can_Msg_struct.data[1] - i -1);
					break;
				}	
				ssid[i] = p_can_union._Can_Msg_struct.data[i+2];
			}
			printf("wifi账号 = %s \n", ssid);
			printf("wifi密码 = %s \n", psk);
			sprintf(logbuf, "wifi账号 = %s \n", ssid);
			write_plate_write_can_log(logbuf);
			sprintf(logbuf, "wifi密码 = %s \n", psk);

			memset(logbuf,0,500);
			sprintf(logbuf,"%s \n\n","ctrl_interface=/var/run/wpa_supplicant");
			sprintf(logbuf + strlen(logbuf), "%s \n","ap_scan=1");
			sprintf(logbuf + strlen(logbuf), "%s \n","network={");
			sprintf(logbuf + strlen(logbuf), "         ssid=\"%s\" \n", ssid);
			sprintf(logbuf + strlen(logbuf), "         psk=\"%s\" \n", psk);
			sprintf(logbuf + strlen(logbuf), "%s \n", "}");

			printf("文件写入数据 = \n%s \n", logbuf);
			//wifi信息写入配置文件
			write_wifi_msg_file(logbuf);
			//重新配置wifi
			system("ifconfig wlan0 down");
			system("kill -9 $(pidof wpa_supplicant)");
			system("/opt/mc_shell/wifi_connect.sh");
			// //开始获取NTP时间
			// set_start_get_ntp();

			//开始获取uuid
			struct timeval tv;
			time_t tt;
			char* p=NULL;
			tv.tv_sec=120;
			tv.tv_usec=0;
			int err;
			while (1)
			{
				sleep(2);
				status = sqlite_read_device_satus();
				debug_print("devMsg.status = %d \n",status);
				if(status >= 1 && (get_net_status() == 1)){
					debug_print("获取到UUID \n");
					frdup.can_dlc = 5;
					frdup.data[0] = 0xAA;
					frdup.data[1] = 0x31;
					frdup.data[2] = 0xD4;
					frdup.data[3] = 0xC1;
					frdup.data[4] = 0xA5;
					send_can_data(frdup);
					break;
				}
			}
			can_rec_data_len = 0;
		break;

		case GET_UUID_CMD://获取到UUID
			// devMsg = sqlite_read_devMsg_from_config_db();
			// debug_print("读取UUId = %s len =%d\n",devMsg.uuid ,strlen(devMsg.uuid));

			// frdup.can_dlc = strlen(devMsg.uuid)+4;
			// frdup.data[0] = 0xAA;
			// memcpy(frdup.data+1,devMsg.uuid,strlen(devMsg.uuid));
			// crc_result = crc16_calc(devMsg.uuid,strlen(devMsg.uuid));
			// frdup.data[strlen(devMsg.uuid)+1] =crc_result>>8;
			// frdup.data[strlen(devMsg.uuid)+2] = crc_result&0x00ff;
			// frdup.data[strlen(devMsg.uuid)+3] = 0xA5;
			// send_can_data(frdup);
			//char *buf =	"49608095-8cad-4300-8f6d-aca84fca8da6";
			//memcpy(jobId, buf, sizeof(jobId));
			status = sqlite_read_device_satus();//获取当前设备状态
			if(status>1)
			{
				sqlite_update_dev_status_config_db(1);
				// system("kill -9 $(pidof WriteDisk)");
				// sleep(2);
				// system("/home/meican/WriteDisk");//重启QT
				// sleep(6);
				// debug_print("获取UUID 重新启动QT \n\n");
				system("/home/meican/rebootQt.sh");//
			}
			frdup.can_dlc = 5;
			frdup.data[0] = 0xAA;
			frdup.data[1] = 0x31;
			frdup.data[2] = 0xD4;
			frdup.data[3] = 0xC1;
			frdup.data[4] = 0xA5;
			send_can_data(frdup);
				
		break;

		case CHECK_BLUE_CMD://检测蓝牙
			mSndMsg.datalen = 4;
			mSndMsg.cmd = WRPLATE_FACTORY_CHECK_CMD;
			mSndMsg.data[0] = BLUE_CHECK;//
			mSndMsg.data[1] = 0;//
			send_data_to_qt_direct(mSndMsg);//直接发送应答回复到
			memset(blue_test_name, 0, 100);
			memcpy(blue_test_name, p_can_union._Can_Msg_struct.data+2, p_can_union._Can_Msg_struct.data[1]);
			printf("蓝牙信息 = %s \n", blue_test_name);
			sprintf(logbuf,"蓝牙信息 = %s \n", blue_test_name);

			//搜索蓝牙
			// char *cmd = "hcitool scan ";
			char *cmd = tempbuf;
			memset(cmd,0,sizeof(tempbuf));
			sprintf(cmd,"hcitool scan | grep %s",blue_test_name);
			char a8Result[1024] = {0};
			int ret = 0;
			int counter = 0;
			for(counter = 0;counter < blue_detect_counter;counter ++){
				ret  = _System(cmd, a8Result, sizeof(a8Result));
				printf("ret = %d; a8Result = %s; length = %d \n", ret, a8Result, strlen(a8Result));
				if(!ret){
					break;
				}
				sleep(1);

			}
			if(!ret) {
				mSndMsg.data[1] = 1;//蓝牙检测成功
			} else {
				mSndMsg.data[1] = 2;//蓝牙检测失败
			}
			send_data_to_qt_direct(mSndMsg);//直接发送应答回复到
		break;

		case CHECK_BEEP_CMD://检测蜂鸣器
			mSndMsg.datalen = 4;
			mSndMsg.cmd = WRPLATE_FACTORY_CHECK_CMD;
			mSndMsg.data[0] = BEEP_CHECK;//
			mSndMsg.data[1] = 0;//
			send_data_to_qt_direct(mSndMsg);//直接发送应答回复到Q

			system("echo 4 > /sys/class/gpio/unexport");
			system("echo 4 > /sys/class/gpio/export");
			system("echo out > /sys/class/gpio/gpio4/direction");
			system("echo 1 > /sys/class/gpio/gpio4/value");
			//写log
			sprintf(logbuf, "%s", "蜂鸣器检测");
		break;

		case CHECK_RFID_CMD://检测读卡
			mSndMsg.datalen = 4;
			mSndMsg.cmd = WRPLATE_FACTORY_CHECK_CMD;
			mSndMsg.data[0] = RFID_CHECK;//
			mSndMsg.data[1] = 0;//
			send_data_to_qt_direct(mSndMsg);//直接发送应答回复到Q
			sprintf(logbuf, "%s", "读盘检测");
			rfidTestFlag = true;//工厂读卡测试开启
		break;

		case CHECK_MOTOR_CMD://检测电机
			mSndMsg.datalen = 4;
			mSndMsg.cmd = WRPLATE_FACTORY_CHECK_CMD;
			mSndMsg.data[0] = MOTOR_CHECK;//
			mSndMsg.data[1] = 0;//
			send_data_to_qt_direct(mSndMsg);//直接发送应答回复到Q
			system("echo 8 > /sys/class/gpio/unexport");
			system("echo 8 > /sys/class/gpio/export");
			system("echo out > /sys/class/gpio/gpio8/direction");
			system("echo 1 > /sys/class/gpio/gpio8/value");
			sprintf(logbuf, "%s", "震动检测");
		break;

		case CHECK_VOICE_CMD://检测语音播放
			// if(mct_dev_bak >1)
			// 	sleep(7);
			printf("语音测试 \n\n");
			//sqlite_update_dev_status_config_db(1);
			mSndMsg.datalen = 4;
			mSndMsg.cmd = WRPLATE_FACTORY_CHECK_CMD;
			mSndMsg.data[0] = VOICE_CHECK;//
			mSndMsg.data[1] = 0;//
			send_data_to_qt_direct(mSndMsg);//直接发送应答回复到Q
			sprintf(logbuf, "%s", "语音检测");
			write_plate_write_can_log(logbuf);
			system("/home/meican/music.sh");
			system("aplay /home/meican/test.wav");
		break;

		case CHECK_REBOOT_CMD://重启测试
			frdup.can_dlc = 5;
			frdup.data[0] = 0xAA;
			frdup.data[1] = 0x31;
			frdup.data[2] = 0xD4;
			frdup.data[3] = 0xC1;
			frdup.data[4] = 0xA5;
			send_can_data(frdup);
			//system("/home/meican/msgclean");
			sleep(1);
			sprintf(logbuf, "%s", "重启检测");
			status = sqlite_read_device_satus();//获取当前设备状态
			if(status < mct_dev_bak)//重启前状态小于测试前备份状态则修改回测试前状态
			{
				sqlite_update_dev_status_config_db(mct_dev_bak);
			}		
			system("reboot");
		break;

		case CHECK_LED_CMD://灯带测试
			mSndMsg.datalen = 4;
			mSndMsg.cmd = WRPLATE_FACTORY_CHECK_CMD;
			mSndMsg.data[0] = LED_CHECK;//
			mSndMsg.data[1] = 0;//
			send_data_to_qt_direct(mSndMsg);//直接发送应答回复到Q
			system("echo 9 > /sys/class/gpio/unexport");
			system("echo 9 > /sys/class/gpio/export");
			system("echo out > /sys/class/gpio/gpio9/direction");
			system("echo 1 > /sys/class/gpio/gpio9/value");
			sprintf(logbuf, "%s", "灯带检测");
		break;

		case CHECK_CAN_CMD://CAN指令检测
			printf("CAN指令检测\n\n");
			
			// frdup.can_dlc = 5;
			// frdup.data[0] = 0xAA;
			// frdup.data[1] = 0x31;
			// frdup.data[2] = 0xD4;
			// frdup.data[3] = 0xC1;
			// frdup.data[4] = 0xA5;
			// send_can_data(frdup);
			// printf("CAN指令检测成功 \n\n");
			// can_rec_data_len = 0;
			// can_rec_status = 0;
			status = sqlite_read_device_satus();//获取当前设备状态
			mct_dev_bak = status;//写盘器初始状态备份
			
			if(status >1)
			{
				//sqlite_update_dev_sn_config_db(devSn,code);
				//while(sqlite_update_dev_status_config_db(1))//修改配置数据库设备状态到0
				sqlite_update_dev_status_config_db(1);
				//mct_dev_bak = status;//写盘器初始状态备份
				// system("kill -9 $(pidof WriteDisk)");
				// sleep(4);
				// system("/home/meican/WriteDisk");//重启QT
				// sleep(6);
				system("/home/meican/rebootQt.sh");//
				
				// sendbuf[0] = 1;
				// aws_send_data_to_qt(WRPLATE_DEV_STATUS_CMD,sendbuf,1);
			}
			
			// frdup.can_dlc = 5;
			// frdup.data[0] = 0xAA;
			// frdup.data[1] = 0x31;
			// frdup.data[2] = 0xD4;
			// frdup.data[3] = 0xC1;
			// frdup.data[4] = 0xA5;
			// send_can_data(frdup);
			// printf("CAN指令检测成功 \n\n");
			// can_rec_data_len = 0;
			// can_rec_status = 0;
			// system("ip link set can0 down");
			// sleep(1);
			// system("/home/meican/setcan.sh");
			// sleep(3);
			// close(fileFd);
			// can_init() ;//fileFd

			frdup.can_dlc = 5;
			frdup.data[0] = 0xAA;
			frdup.data[1] = 0x31;
			frdup.data[2] = 0xD4;
			frdup.data[3] = 0xC1;
			frdup.data[4] = 0xA5;
			send_can_data(frdup);
			printf("CAN指令检测成功 \n\n");
			can_rec_data_len = 0;
			can_rec_status = 0;
			status = sqlite_read_device_satus();//获取当前设备状态
			mct_dev_bak = status;//写盘器初始状态备份
		break;

		// case KEY_TEST_CMD://空指令
			
		// break;
	}
	write_plate_write_can_log(logbuf);
}

/*==================================================================================
* 函 数 名： get_fatory_rfid_test_flag
* 参    数：
* 功能描述:  获取读卡测试标记
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/8/27
==================================================================================*/
bool get_fatory_rfid_test_flag(void)
{
	return rfidTestFlag;
}

/*==================================================================================
* 函 数 名： set_fatory_rfid_test_flag
* 参    数：
* 功能描述:  设置读卡测试标记
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/8/27
==================================================================================*/
void set_fatory_rfid_test_flag(bool status)
{
	rfidTestFlag = status;
}

/*==================================================================================
* 函 数 名： receive_can_msg_data_task
* 参    数：
* 功能描述:  can任务
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/8/27
==================================================================================*/
void receive_can_msg_data_task(void)
{
	uint8_t logbuf[200];
    int ret,i;
    struct can_frame frdup;
    fd_set rset;

    FD_ZERO(&rset);
    FD_SET(fileFd, &rset);

    ret = read(fileFd, &frdup, sizeof(frdup));
    if (ret < sizeof(frdup)) {
        myerr("read failed");
        return ;
    }
    if (frdup.can_id & CAN_ERR_FLAG) {/* 出错设备错误 */
        handle_err_frame(&frdup);
        myerr("CAN device error");
    }
   
    //can 数据解析
    debug_print("can 接收数据 = ");
    for (i = 0; i < frdup.can_dlc; i++)
	{
		debug_print("%02x ", frdup.data[i]);
	}	
    debug_print("\n");

	//写log
	HexToStr(logbuf, frdup.data, frdup.can_dlc);	
    write_plate_write_can_log(logbuf);
	//工厂检测数据分析
	factory_check_data_analysis(frdup);

    //can 发送数据
    //send_can_data(frdup); 

	// 震动测试
	// system("echo 8 > /sys/class/gpio/unexport");
	// system("echo 8 > /sys/class/gpio/export");
	// system("echo 1 > /sys/class/gpio/gpio8/value");
	// sleep(1);
	// system("echo 0 > /sys/class/gpio/gpio8/value");
	// sleep(1);
}

/*==================================================================================
* 函 数 名： send_can_data
* 参    数：
* 功能描述:  can总线发送数据
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/8/27
==================================================================================*/
void send_can_data(struct can_frame frdup)
{
    int ret = 0,i=0,len = 0;
	char senddata[8] = {0};
	struct can_frame tempfrdup;

	printf("send_can_data = ");
	// for(i=0;i<frdup.can_dlc;i++){
	// 	printf("%02x ",frdup.data[i]);
	// }

	// for(i=0;i<frdup.can_dlc/8;i++)
	// {
	// 	tempfrdup.can_dlc = i*8+8;
	// 	memcpy(tempfrdup.data,frdup.data+i*8, 8);
	// 	ret = write(fileFd, &tempfrdup, sizeof(tempfrdup));
	// 	if (ret < 0) {
	// 		myerr("write failed");
	// 		return ;
	// 	}
	// 	usleep(100);
	// }

	// tempfrdup.can_dlc = frdup.can_dlc%8;
	// memcpy(tempfrdup.data,frdup.data+frdup.can_dlc/8, frdup.can_dlc%8);
	// ret = write(fileFd, &tempfrdup, sizeof(tempfrdup));
	// if (ret < 0) {
	// 	myerr("write failed");
	// 	return ;
	// }

	ret = write(fileFd, &frdup, sizeof(frdup));
	if (ret < 0) {
		myerr("write failed");
		return ;
	}
    
}

/*==================================================================================
* 函 数 名： can_init
* 参    数：
* 功能描述:  can初始化
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/8/27
==================================================================================*/
void can_init(void) //fileFd
{
   	int ret;
   	struct sockaddr_can addr;
   	struct ifreq ifr;

	srand(time(NULL));
   	fileFd = socket(PF_CAN, SOCK_RAW, CAN_RAW);
   	if (fileFd < 0) {
       	perror("socket PF_CAN failed");
       	return ;
   	}

   	strcpy(ifr.ifr_name, "can0");
   	ret = ioctl(fileFd, SIOCGIFINDEX, &ifr);
   	if (ret < 0) {
       	perror("ioctl failed");
       	return ;
   	}
   	addr.can_family = PF_CAN;
   	addr.can_ifindex = ifr.ifr_ifindex;

   	ret = bind(fileFd, (struct sockaddr *)&addr, sizeof(addr));
   	if (ret < 0) {
       	perror("bind failed");
       	return ;
   	}
	if (1) {
		struct can_filter filter[2];
		filter[0].can_id = 0x002 | CAN_EFF_FLAG;
		filter[0].can_mask = 0xFFF;

		filter[1].can_id = 0x20F | CAN_EFF_FLAG;
		filter[1].can_mask = 0xFFF;

		ret = setsockopt(fileFd, SOL_CAN_RAW, CAN_RAW_FILTER, &filter, sizeof(filter));
		if (ret < 0) {
			perror("setsockopt failed");
			return ;
		}
	}
	printf("CAN初始化成功 \n\n");
}

/*==================================================================================
* 函 数 名： can_test
* 参    数：
* 功能描述:  can测试
* 返 回 值：
* 备    注： None
* 作    者： lc
* 创建时间： 2021/6/29
==================================================================================*/
int can_test(void)
{
   	int ret;
   	struct sockaddr_can addr;
   	struct ifreq ifr;
    int s;
	
	srand(time(NULL));
   	s = socket(PF_CAN, SOCK_RAW, CAN_RAW);
   	if (s < 0) {
       	perror("socket PF_CAN failed");
       	return 1;
   	}

   	strcpy(ifr.ifr_name, "can0");
   	ret = ioctl(s, SIOCGIFINDEX, &ifr);
   	if (ret < 0) {
       	perror("ioctl failed");
       	return 1;
   	}

   	addr.can_family = PF_CAN;
   	addr.can_ifindex = ifr.ifr_ifindex;

   	ret = bind(s, (struct sockaddr *)&addr, sizeof(addr));
   	if (ret < 0) {
       	perror("bind failed");
       	return 1;
   	}
	if (1) {
		struct can_filter filter[2];
		filter[0].can_id = 0x200 | CAN_EFF_FLAG;
		filter[0].can_mask = 0xFFF;

		filter[1].can_id = 0x20F | CAN_EFF_FLAG;
		filter[1].can_mask = 0xFFF;

		ret = setsockopt(s, SOL_CAN_RAW, CAN_RAW_FILTER, &filter, sizeof(filter));
		if (ret < 0) {
			perror("setsockopt failed");
			return 1;
		}
	}
	test_can_rw(s, master);

	close(s);
	return 0;
}
