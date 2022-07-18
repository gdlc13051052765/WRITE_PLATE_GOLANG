#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "sqlite3.h"
#include "sqliteTask.h"
#include "debug_print.h"
#include "rewrCardTask.h"
#include "msgTask.h"
#include "canTask.h"
#include "beepMotor.h"

//餐盘标签信息
static rfalTagRes tag[EXAMPLE_RFAL_POLLER_DEVICES];

#define MAX_HEX_STR         4
#define MAX_HEX_STR_LENGTH  128
#define POLL_LABEL_TIMEST   30000//寻卡延时30ms
static uint32_t tag_cstm_id_table = 0x0000;		//每一位代表分配的情况

static _Tag_Context mTag_Context;
static uint16_t meicanIdentificationCode = 215;//美餐餐盘识别码
	 
#define CLEAR_TAG_CSTM_ID(index)		do{(index == 0x0F)?(tag_cstm_id_table=0):(tag_cstm_id_table &= ~(0X0001<<index));}while(0)	//清空标签唯一ID，当标签个数为0时候，清空ID

//获取标签个数
#define GET_TAG_NUM()		mTag_Context.total_tag_num
char hexStr[MAX_HEX_STR][MAX_HEX_STR_LENGTH];
uint8_t hexStrIdx = 0;

//
static char* hex2str(unsigned char *data, size_t dataLen)
{ 
  unsigned char * pin = data;
  const char * hex = "0123456789ABCDEF";
  char * pout = hexStr[hexStrIdx];
  uint8_t i = 0;
  uint8_t idx = hexStrIdx;

  if(dataLen == 0) {
    pout[0] = 0;     
  } else {
    for(; i < dataLen - 1; ++i) {
      *pout++ = hex[(*pin>>4)&0xF];
      *pout++ = hex[(*pin++)&0xF];
    }
    *pout++ = hex[(*pin>>4)&0xF];
    *pout++ = hex[(*pin)&0xF];
    *pout = 0;
  }    
  hexStrIdx++;
  hexStrIdx %= MAX_HEX_STR;
  
  return hexStr[idx];
}

/*==================================================================================
* 函 数 名： rfid_context_init
* 参    数： None
* 功能描述:  数据结构初始化
* 返 回 值： None
* 备    注： 
* 作    者： xiaozh
* 创建时间： 2019-09-24 184722
==================================================================================*/
static void rfid_context_init(void)
{
  uint8_t i;

	mTag_Context.total_tag_num = 0;	//标签数量
	mTag_Context.read_tag_num = 0;	//标签数量
	mTag_Context.use_state = 0;			//当前存储是否占用
	
	for(i=0; i<MAX_TAG_NUM; i++) {
		mTag_Context.new_tag_info[i].is_use = 0;
		mTag_Context.new_tag_info[i].tag_state = NULL_STA;
		memset(mTag_Context.new_tag_info[i].uid, 0xFF, TAG_LENGTH);
		memset(mTag_Context.new_tag_info[i].block, 0xFF, TAG_LENGTH);
		
		mTag_Context.old_tag_info[i].is_use = 0;
		mTag_Context.old_tag_info[i].cstm_tag_id.cstm_id = 0;
		mTag_Context.old_tag_info[i].tag_state = NULL_STA;
		memset(mTag_Context.old_tag_info[i].uid, 0xFF, TAG_LENGTH);
		memset(mTag_Context.old_tag_info[i].block, 0xFF, TAG_LENGTH);
	}
}

/*==================================================================================
* 函 数 名： context_clear
* 参    数： None
* 功能描述:  数据结构清空
* 返 回 值： None
* 备    注： 
* 作    者： xiaozh
* 创建时间： 2019-09-24 184722
==================================================================================*/
static void context_clear(void)
{
  uint8_t i;

	mTag_Context.total_tag_num = 0;
	mTag_Context.read_tag_num = 0;	//标签数量
	mTag_Context.use_state = 0;			//当前存储是否占用
	
	for(i=0; i<MAX_TAG_NUM; i++) 
	{
		mTag_Context.old_tag_info[i].is_use = 0;
		mTag_Context.old_tag_info[i].tag_state = NULL_STA;
		memset(mTag_Context.old_tag_info[i].uid, 0xFF, TAG_LENGTH);
		memset(mTag_Context.old_tag_info[i].block, 0xFF, TAG_LENGTH);
	}
}

/*==================================================================================
* 函 数 名： get_cstm_tag_id
* 参    数： None
* 功能描述:  给新接入的标签分配一个ID号
* 返 回 值： None
* 备    注： 
* 作    者： xiaozh
* 创建时间： 2019-11-05 114204
==================================================================================*/
static uint8_t get_cstm_tag_id(void)
{
  uint8_t i;

	for(i=0; i<0x0F; i++) 
	{
		if((tag_cstm_id_table & (0x0001<<i)) == 0) {
			tag_cstm_id_table |= (0x0001<<i);
			return i;
		}
	}
	return 0x0F;	//空间已满
}

/*==================================================================================
* 函 数 名： get_cstm_tag_id
* 参    数： None
* 功能描述:  给新接入的标签分配一个ID号
* 返 回 值： None
* 备    注： 
* 作    者： xiaozh
* 创建时间： 2019-11-05 114204
==================================================================================*/
static uint8_t delete_cstm_tag_id(uint8_t index)
{
 	CLEAR_TAG_CSTM_ID(index); 
	return 0;	//空间已满
}

/*==================================================================================
* 函 数 名： find_tag_id_node
* 参    数： None
* 功能描述:  根据ID号查找标签索引
* 返 回 值： 返回索引
* 备    注： 
* 作    者： xiaozh
* 创建时间： 2019-11-05 120716
==================================================================================*/
static uint8_t find_tag_id_node(uint8_t cstm_id)
{
  uint8_t i;

	for(i=0; i<MAX_TAG_NUM; i++) 
	{
		if(mTag_Context.old_tag_info[i].is_use)
		{
			if(mTag_Context.old_tag_info[i].cstm_tag_id.cstm_id == cstm_id)
				return i;
		}
	}
	return 0xFF;	//空间已满
}

/*==================================================================================
* 函 数 名： find_avalib_node
* 参    数： None
* 功能描述:  查找空闲可以的节点
* 返 回 值： None
* 备    注： 
* 作    者： xiaozh
* 创建时间： 2019-09-25 145139
==================================================================================*/
static uint8_t find_avalib_node(void)
{
  uint8_t i;

	for(i=0; i<MAX_TAG_NUM; i++)
	{
		if(!mTag_Context.old_tag_info[i].is_use)
			return i;
		
	}
	return 0xFF;	//没有查找到
}

/*==================================================================================
* 函 数 名： delete_node_index
* 参    数： None
* 功能描述:  删除节点
* 返 回 值： None
* 备    注： 
* 作    者： xiaozh
* 创建时间： 2019-10-10 180604
==================================================================================*/
static uint8_t delete_node_index(void *info, uint8_t index)
{ 
	_pTag_Context pmsg = info;
	
	pmsg->old_tag_info[index].is_use = 0;
	pmsg->old_tag_info[index].tag_state = NULL_STA;
	
	pmsg->old_tag_info[index].is_update = 0; 
	pmsg->old_tag_info[index].tag_up_state = (_Tag_Sta)0;
	delete_cstm_tag_id(pmsg->old_tag_info[index].cstm_tag_id._bit.id_code);
	pmsg->old_tag_info[index].cstm_tag_id.cstm_id = 0;
	
	if(pmsg->total_tag_num > 0) {
		pmsg->total_tag_num--;
	} else {
		pmsg->total_tag_num = 0;
	}
	
	return 0;
}

/*==================================================================================
* 函 数 名： find_alike_card
* 参    数： None
* 功能描述:  查找相同id号的标签
* 返 回 值： 如果有相同的则返回索引，否则返回0xff
* 备    注： 
* 作    者： xiaozh
* 创建时间： 2019-10-10 174600
==================================================================================*/
static uint8_t find_alike_card(void *info, uint8_t *buff, uint16_t len)
{
  uint8_t i;
	_pTag_Context pmsg = info;

	for(i=0; i<MAX_TAG_NUM; i++)
	{
		if(pmsg->old_tag_info[i].is_use) //当前位置使用，且不为新接入的标签
		{
			if(memcmp(pmsg->old_tag_info[i].uid, buff, len) == 0)	//相等,比较到相同的标签
				return i;
		}
	}
	return 0xFF;
}

/*==================================================================================
* 函 数 名： add_new_item
* 参    数： None
* 功能描述:  加入新节点
* 返 回 值： None
* 备    注： 
* 作    者： xiaozh
* 创建时间： 2019-10-10 174600
==================================================================================*/
static uint8_t add_new_item(void *info, uint8_t *card_id, uint16_t len)
{ 
	uint8_t f_index = 0;
	_pTag_Context pmsg = info;
 
	f_index = find_avalib_node();

	//拷贝标签ID
	memcpy(pmsg->old_tag_info[f_index].uid, card_id, TAG_UID_LENS);	//拷贝标签号
	pmsg->old_tag_info[f_index].tag_state = ENTRY_BLOCK_FAIL_STA;
	pmsg->old_tag_info[f_index].is_use = 0x01;
	
	//变量增加
	pmsg->total_tag_num++;
	
	//给新增加的标签分配一个ID号 
	pmsg->old_tag_info[f_index].cstm_tag_id._bit.id_code = (uint8_t)(get_cstm_tag_id()&0x0F);	//获取唯一ID
//	pmsg->old_tag_info[f_index].cstm_tag_id._bit.cstm_crc = crc4_itu(card_id, TAG_UID_LENS);//获取标签校验码
	pmsg->old_tag_info[f_index].tag_up_state = NEW_ENTRY_STA;	//标记更新状态
	pmsg->old_tag_info[f_index].is_update = 0x00;	//标记更新状态

	return f_index;
}

/*==================================================================================
* 函 数 名： find_lose_card
* 参    数： None
* 功能描述:  查询丢失的卡号
* 返 回 值： None
* 备    注： 
* 作    者： xiaozh
* 创建时间： 2019-10-10 174600
==================================================================================*/
static uint8_t find_lose_card(void *info, uint32_t opt_index)
{
  uint8_t i;
	_pTag_Context pmsg = info;

	for(i=0; i<MAX_TAG_NUM; i++)
	{
		if(pmsg->old_tag_info[i].is_use) //当前位置使用
		{
			if((opt_index & (0x00000001<<i)) == 0)		//当前节点没有被操作过
			{
				if(pmsg->old_tag_info[i].tag_state == EXIT_STA)	{	//如果上次已经为退出状态
					pmsg->old_tag_info[i].tag_state = NULL_STA;		//则认为标签离开，并删除节点
					delete_node_index(info, i);	//删除节点
				} else {
					pmsg->old_tag_info[i].tag_state = EXIT_STA;		//则认为标签进入将要退出状态
				}
			}
		}
	}
	return 0;
}

/*==================================================================================
* 函 数 名： tag_compare_remark
* 参    数： None
* 功能描述:  返回标记的节点
* 返 回 值： None
* 备    注： 
* 作    者： xiaozh
* 创建时间： 2019-09-24 185604
==================================================================================*/
static uint8_t tag_compare_remark(void *info, rfalTagRes* cards)
{
	uint8_t r_index = 0; 
	_pTag_Context pmsg = info;
	uint8_t block_buff[16];  /* Flags + Block Data + CRC */
	uint16_t read_block_len = 0;

	//查找是否有相同ID号的
	if((r_index = find_alike_card(info, cards->uid, TAG_UID_LENS)) != 0xFF)	{//有相同的
		pmsg->old_tag_info[r_index].tag_state = EXIST_STA;	//标签存在	
		return r_index;
	} else {//没有找到相同的标签号
		//新接入的标签号
		//拷贝标签ID
		r_index = add_new_item(info, cards->uid, TAG_UID_LENS); 
		pmsg->old_tag_info[r_index].tag_state = ENTRY_BLOCK_OK_STA;
		return r_index;	//记录操作过的节点
	}
}

/*==================================================================================
* 函 数 名： compare_all_tag
* 参    数： None
* 功能描述:  对所有标签对比，并序列化
* 返 回 值： None
* 备    注： 
* 作    者： xiaozh
* 创建时间： 2019-09-24 185604
==================================================================================*/
static void compare_all_tag(void *info, rfalTagRes* cards, uint8_t card_num)
{
	uint8_t r_index = 0, i;
	uint32_t opt_node_index = 0;
	_pTag_Context pmsg = info;
	uint8_t block_buff[16];  /* Flags + Block Data + CRC */
	uint16_t read_block_len = 0;

	if(pmsg ->total_tag_num == 0)	//如果没有一个标签，直接存储
	{
		CLEAR_TAG_CSTM_ID(0x0F);	//清空步进值		 
		//添加新增标签
		for(i = 0; i < card_num; i++)
		{
			//拷贝标签ID
			r_index = add_new_item(info, cards->uid, TAG_UID_LENS); 
		}
		//置位总的标签数量
		pmsg->total_tag_num = card_num;
		return;
	}

	//进行单个标签操作
	for(i=0; i<card_num; i++)
	{
		r_index = tag_compare_remark(info, &cards[i]); 
		opt_node_index |= (0x00000001<<r_index);	//记录操作过的节点
	}
	 
	//查询丢失节点
	find_lose_card(info, opt_node_index);
} 

//==================================================================================================
// NAME: void rfid_find_tag(void)
//
// BRIEF:扫描卡，
// INPUTS: none
// OUTPUTS: none         
//====================================================================================================
static void rfid_find_tag(void* info)
{ 
	static uint8_t read_zero_count = 0;		//读取到0个标签的次数   
	uint8_t actcnt; 

  actcnt = rfal_find_tag(tag);//读取标签
	compare_all_tag(info, tag, actcnt); 
	
	if(actcnt != 0) { 
		//进行数据分组标记拷贝
		compare_all_tag(info, tag, actcnt);  
		read_zero_count = 0;
	} else {
		//在最后一张标签退厂时候 
		if(GET_TAG_NUM() > 0) {
			read_zero_count++;
			if(read_zero_count > MAX_READ_ZERO_NUM)	//如果多次读取为空，则清空缓存
			{
				read_zero_count = 0;
				context_clear();
				debug_print("lost all tag\n");
			}
		}
	}
}

/*==================================================================================
* 函 数 名： nfc_read_card_init
* 参    数： None
* 功能描述:  nfc读写器初始化
* 返 回 值： None
* 备    注： 初始化成功返回0
* 作    者： lc
* 创建时间： 2021-04-20 
==================================================================================*/
int nfc_read_card_init(void)
{
	//读取餐盘识别码
	meicanIdentificationCode = sqlite_read_meican_indent_code();
	debug_print("美餐餐盘识别码 = %d\n", meicanIdentificationCode);
	return rfal_init();
}

static void beep_open(int num)
{
	// int i=0 ;

	// system("echo 4 > /sys/class/gpio/unexport");
	// system("echo 4 > /sys/class/gpio/export");
	// system("echo out > /sys/class/gpio/gpio4/direction");
	// for(i=0; i<num; i++)
	// {
	// 	system("echo 1 > /sys/class/gpio/gpio4/value");
	// 	usleep(50000);
	// 	system("echo 0 > /sys/class/gpio/gpio4/value");
	// }
	beep_on(num);
}

/*=======================================================================================
* 函 数 名： nfc_write_plate_task
* 参    数： None
* 功能描述:  写盘器消费流程，寻卡，写卡，数据库读写数据任务，在go主文件中被作为一个线程任务调用
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-20 
==========================================================================================*/
static uint8_t writePlataStatus = 0;//写盘状态机
static uint8_t filterNum = 3;//读标签过滤次数
static uint8_t tagnumbak[8];//标签个数备份

int nfc_write_plate_task(void)
{
  uint8_t tag_num,read_block_len,i;
  uint8_t block_buff_Read[20] = {0};
  uint8_t Write_Data[20] = {0};
  char logbuf[200];
  int dishid = 0;
  dishMsgSt dishMsg;
  qtdata_t sndMsg;

  //工厂读卡测试
  if(get_fatory_rfid_test_flag() == true) {
	  nfc_write_plate_rfid_test();
	  return;
  }
  //获取写盘器状态非工作状态停止写盘
  // if(get_aws_iot_dev_status() != C_SITE_BIND_OK_STATUS)
  // 	return;
  //获取是否停止写盘状态
  if(!get_stop_write_palte_status())//收到停止写盘命令停止写盘
  	return;

  switch(writePlataStatus)
  {
    case 0: 
      sndMsg.datalen = 0x03;
      sndMsg.cmd = WRPLATE_STAS_CMD;

      for(i=0; i<filterNum; i++) 
			{
        //rfid_find_tag(&mTag_Context);//读取标签
        tag_num = rfal_find_tag(tag);//读取标签
        tagnumbak[i] = tag_num;   
        usleep(POLL_LABEL_TIMEST);//延时30ms
      }
      for(i=0; i<filterNum; i++) //多次读取标签的个数不一致返回重新读标签
			{
        if(tagnumbak[i] != tag_num)
          return;
      }
      debug_print("rfid total tag number = %d\n", tag_num);
      if(tag_num) {
        sprintf(logbuf,"rfid total tag number = %d", tag_num);
        write_plate_write_rfid_log(logbuf);
      }
      
      if(!tag_num) {//无标签存在
        return WRITEPLATE_NULL_ERR;
      }
	   //多于允许写盘的标签存在
      if(tag_num > MAX_WRITE_PLATE) {
        debug_print("multiple tags exist \n");
        sprintf(logbuf, "%s", "multiple tags exist");
        write_plate_write_rfid_log(logbuf);
        sndMsg.data[0] = WRITEPLATE_MUL_ERR;
        //qt_push_data_to_msg(sndMsg);//发送写盘状态到发送队列
        send_data_to_qt_direct(sndMsg);
        writePlataStatus = 2;
		  	beep_open(3);
        return WRITEPLATE_MUL_ERR;
      } else {
				writePlataStatus = 1;//寻到一张标签跳转到写标签流程		
			}
    break;

    case 1:
      tag_num = rfal_find_tag(tag);//读取标签
      if(!tag_num) { //无标签存在
        writePlataStatus = 0;
        return WRITEPLATE_NULL_ERR;
      }
      //从数据库读取写盘信息
      dishMsg = sqlite_read_writePlateMsg_from_dishmenu();
	   //读取菜单信息失败
      if(dishMsg.res != SQLITE_OK ) {
        debug_print("read menu fail \n");
        sprintf(logbuf, "%s", "read menu fail");
        write_plate_write_rfid_log(logbuf);
        sndMsg.data[0] = WRITEPLATE_NULL_ERR;
        //qt_push_data_to_msg(sndMsg);//发送写盘状态到发送队列
		    send_data_to_qt_direct(sndMsg);
        writePlataStatus = 2;//跳转到取走标签状态机
		    beep_open(3);
        return WRITEPLATE_ERROR;
      }
      //开始写菜品信息到标签
      for(i=0; i<tag_num; i++) 
			{  
        debug_print("tag uid = %s \n", hex2str(tag[i].uid, 8));
        sprintf(logbuf,"tag uid = %s", hex2str(tag[i].uid, 8));
        write_plate_write_rfid_log(logbuf);

				read_block_len = rfal_read_single_block(tag[i].uid, 3, block_buff_Read);
        debug_print("read block3 data = %s \n", hex2str(block_buff_Read, read_block_len));
			  //读取block数据
        read_block_len = rfal_read_single_block(tag[i].uid, 2, block_buff_Read);
				debug_print("read block2 data = %s \n", hex2str(block_buff_Read, read_block_len));
				sprintf(logbuf, "read block2 data = %s", hex2str(block_buff_Read, read_block_len));
        write_plate_write_rfid_log(logbuf);
        if(!read_block_len || block_buff_Read[0] != meicanIdentificationCode) {
          sndMsg.data[0] = WRITEPLATE_READ_ERR;//读标签失败
          //qt_push_data_to_msg(sndMsg);//发送写盘状态到发送队列
		      send_data_to_qt_direct(sndMsg);
          writePlataStatus = 2;//跳转到取走标签状态机
		  		beep_open(3);
					if(block_buff_Read[0] != meicanIdentificationCode)
					{
						sprintf(logbuf, "%s", "非美餐餐盘");
        		write_plate_write_rfid_log(logbuf);
					}
          return WRITEPLATE_READ_ERR;//读标签失败
        } 
        debug_print("dishMsg.dishid = %d \n",dishMsg.dishid);
				Write_Data[0] = meicanIdentificationCode;//餐盘识别码
        Write_Data[1] = dishMsg.dishid >> 10;
				Write_Data[2] = dishMsg.dishid >> 2;
				Write_Data[3] = dishMsg.dishid << 6;
			  //已经写入无需再写
        // if(!(memcmp(Write_Data, block_buff_Read, 4))) {
        //   debug_print("write block have ok \n");
        //   sndMsg.data[0] = WRITEPLATE_OK;//
        //   //qt_push_data_to_msg(sndMsg);//发送写盘状态到发送队列
		    //   send_data_to_qt_direct(sndMsg);
        //   writePlataStatus = 2;//跳转到取走标签状态机
		  	// 	beep_open(1);
        //   return WRITEPLATE_OK;
        // }
        //写餐品ID信息到block
        if(!(rfal_write_single_block(tag[i].uid, 2, Write_Data, 4))) {
          debug_print("write block ok \n");
          sprintf(logbuf, "%s, write data = %2x %2x %2x %2x", "write block ok ", Write_Data[0], Write_Data[1], Write_Data[2], Write_Data[3]);
          write_plate_write_rfid_log(logbuf);
          sndMsg.data[0] = WRITEPLATE_OK;//
          //qt_push_data_to_msg(sndMsg);//发送写盘状态到发送队列
		      send_data_to_qt_direct(sndMsg);
          writePlataStatus = 2;//跳转到取走标签状态机
		    	beep_open(1);
					rfal_write_single_block(tag[i].uid, 3, "\x00\x00\x00\x00", 4);
					writePlataStatus = 2;//跳转到取走标签状态机
          return WRITEPLATE_OK;//写盘信息成功
        } else {//写盘信息失败
          debug_print("write block fail \n");
          sprintf(logbuf, "%s", "write block fail");
          write_plate_write_rfid_log(logbuf);
          sndMsg.data[0] = WRITEPLATE_ERROR;//
          //qt_push_data_to_msg(sndMsg);//发送写盘状态到发送队列
		      send_data_to_qt_direct(sndMsg);
          writePlataStatus = 2;//跳转到取走标签状态机
		    	beep_open(3);
          return WRITEPLATE_ERROR;//写盘信息失败
        }         
      }
    break;

    case 2: //等待取走标签  
      for(i=0; i<filterNum; i++) 
			{
        tag_num = rfal_find_tag(tag);//读取标签 
        tagnumbak[i] = tag_num;   
        usleep(POLL_LABEL_TIMEST);//延时30ms
		  	debug_print("remove total tag number = %d \n", tag_num);
      }
      // for(i=0; i<filterNum; i++) //多次读取标签的个数不一致返回重新读标签
			// {
      // 	if(tagnumbak[i] != tag_num)
      // 		return;
      // }
      if(!tag_num) {//标签已取走
        sndMsg.datalen = 0x03;
        sndMsg.cmd = WRPLATE_REMOVE_CMD;
		    sndMsg.data[0] = 0;
        //qt_push_data_to_msg(sndMsg);//发送标签离场指令到发送队列
		    send_data_to_qt_direct(sndMsg);
        writePlataStatus = 0;
      }  
      // else {
      //   sleep(2);
      //   sndMsg.datalen = 0x03;
      //   sndMsg.cmd = WRPLATE_REMOVE_CMD;
		  //   sndMsg.data[0] = 0;
      //   //qt_push_data_to_msg(sndMsg);//发送标签离场指令到发送队列
		  //   send_data_to_qt_direct(sndMsg);
      //   writePlataStatus = 0;
      // }
    break;
  }
  return WRITEPLATE_OK;
}

/*=======================================================================================
* 函 数 名： nfc_write_plate_test
* 参    数： None
* 功能描述:  工厂检测读盘测试
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-20 
==========================================================================================*/
int test_tag_num_bak = 0;
int nfc_write_plate_rfid_test(void)
{
	uint8_t tag_num = 0,read_block_len,i;
	uint8_t block_buff_Read[20] = {0};
	uint8_t Write_Data[20] = {0};
	qtdata_t sndMsg;

	sndMsg.datalen = 0x04;
	sndMsg.cmd = WRPLATE_FACTORY_CHECK_CMD;

	for(i=0; i<filterNum; i++) 
	{
		tag_num = rfal_find_tag(tag);//读取标签
		tagnumbak[i] = tag_num;   
		usleep(POLL_LABEL_TIMEST);//延时30ms
	}

	if(tag_num) {
		sndMsg.data[0] = 0xB5;//
		sndMsg.data[1] = tag_num;//标签个数
		if(!test_tag_num_bak) {
			debug_print("rfid total tag number = %d\n", tag_num);
		}
		if(test_tag_num_bak != tag_num ) {
			test_tag_num_bak = tag_num;
			send_data_to_qt_direct(sndMsg);//直接发送读标签成功到QT显示
		}	
	} else {
		if(test_tag_num_bak) {
			debug_print("rfid total tag number = %d\n", tag_num);
			test_tag_num_bak = 0;
			sndMsg.data[0] = 0xB5;//
			sndMsg.data[1] = 0;//标签个数
			send_data_to_qt_direct(sndMsg);//直接发送读标签成功到QT显示
		}
	}
}
