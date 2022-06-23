/*
 * Copyright 2010-2015 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

/**
 * @file subscribe_publish_library_sample.c
 * @brief simple MQTT publish and subscribe on the same topic using the SDK as a library
 *
 * This example takes the parameters from the aws_iot_config.h file and establishes a connection to the AWS IoT 
 * MQTT Platform.
 * It subscribes and publishes to the same topic - "sdkTest/sub"
 *
 * If all the certs are correct, you should see the messages received by the application in a loop.
 *
 * The application takes in the certificate path, host name , port and the number of times the publish should happen.
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <unistd.h>
#include <limits.h>
#include <string.h>

#include "include/aws_iot_config.h"
#include "include/aws_iot_log.h"
#include "include/aws_iot_version.h"
#include "include/aws_iot_mqtt_client_interface.h"
#include "include/aws_iot_shadow_interface.h"
#include "include/aws_iot_jobs_interface.h"

#include "debug_print.h"
#include "sqliteTask.h"
#include "cJSON.h"
#include "cString.h"
#include "msgTask.h"
#include "awsIotTask.h"

#define MAX_LENGTH_OF_UPDATE_JSON_BUFFER 1024
#define HOST_ADDRESS_SIZE 255
#define TIME_OUT_COUNT    4 //超时时间
//网络状态
#define NETWORK_CONNECT    0//联网成功
#define IOT_CONNECT_OK     1//连接iot成功
#define NETWORK_DISCONNECT 2//网络断开

static char certDirectory[PATH_MAX + 1] = "certs";//证书文件
static char HostAddress[HOST_ADDRESS_SIZE] = AWS_IOT_MQTT_HOST;//AWS 服务器地址
static uint32_t port = AWS_IOT_MQTT_PORT;//AWS 服务器端口

// initialize the mqtt client
static AWS_IoT_Client mqttClient;
static jsonStruct_t menuUpdateTimeHandler;
static jsonStruct_t snHandler;
static jsonStruct_t versionHandler;
static jsonStruct_t restaurantIDHandler;
static ShadowInitParameters_t sp ;
static char JsonDocumentBuffer[MAX_LENGTH_OF_UPDATE_JSON_BUFFER];
static size_t sizeOfJsonDocumentBuffer = sizeof(JsonDocumentBuffer) / sizeof(JsonDocumentBuffer[0]);
static int64_t menuUpdateTime = 1711111111111;
static int64_t restaurantID = 2;
static char snDeltaData[SHADOW_MAX_SIZE_OF_RX_BUFFER];
static C_ShadowMsgSt pdev;//shadow thingname clientid
static C_menuMsgSt cmenuMsg;//配置数据库菜单版本
static C_DevMsgSt devMsg;//写盘器配置信息
static bool reportSnFlag = false;//sn 码上报标记
static bool reportRestaurantIDFlag = false;//restaurantID 上报标记
static bool reportmenuUpdateTimeFlag = false;//menuUpdateTime 上报标记
static bool reportromVersionFlag = false;//romVersion 上报标记
static bool getShadowFlag = false;//开机获取当前shandow状态
static char devSn[100];//设备SN码
static char code[100];//设备sn code码
static char version[SHADOW_MAX_SIZE_OF_RX_BUFFER];//固件版本
static bool OTA_UPDATE_STATUS = false;//固件更新状态
static bool REPORT_OTA_STATUS = false;//

static jsmn_parser jsonParser;
static jsmntok_t jsonTokenStruct[MAX_JSON_TOKEN_EXPECTED];
static int32_t tokenCount;
static int iot_connect_status_bak = 0;//iot连接状态备份

static void aws_send_data_to_qt(int cmd, uint8_t *data,int len) ;
/*=======================================================================================
* 函 数 名： reboot_golang
* 参    数： 
* 功能描述:  golang 进程重启
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-07-22 
==========================================================================================*/
void reboot_golang(void)
{
  char logbuf[100];

  sprintf(logbuf,"%s","golang 重启");
  write_plate_write_IOT_log(logbuf);
  system("/home/meican/rebootgolang.sh");
}

static void reboot_qt(void)
{
  char logbuf[100];

  sprintf(logbuf,"%s","qt 重启");
  write_plate_write_IOT_log(logbuf);
  system("kill -9 $(pidof WriteDisk)");
  system("/home/meican/WriteDisk");
}

static void iot_get_pending_callback_handler(AWS_IoT_Client *pClient, char *topicName, uint16_t topicNameLen,
									IoT_Publish_Message_Params *params, void *pData) {
  char logbuf[100];

	IOT_UNUSED(pData);
	IOT_UNUSED(pClient);
	debug_print("\nJOB_GET_PENDING_TOPIC callback");
  sprintf(logbuf,"payload = %s","JOB_GET_PENDING_TOPIC callback");
  write_plate_write_IOT_log(logbuf);
	debug_print("topic: %.*s", topicNameLen, topicName);
	debug_print("payload: %.*s", (int) params->payloadLen, (char *)params->payload);

	jsmn_init(&jsonParser);
	tokenCount = jsmn_parse(&jsonParser, params->payload, (int) params->payloadLen, jsonTokenStruct, MAX_JSON_TOKEN_EXPECTED);
	if(tokenCount < 0) {
		debug_print("Failed to parse JSON: %d", tokenCount);
		return;
	}
	/* Assume the top-level element is an object */
	if(tokenCount < 1 || jsonTokenStruct[0].type != JSMN_OBJECT) {
		debug_print("Top Level is not an object");
		return;
	}
	jsmntok_t *jobs;
	jobs = findToken("inProgressJobs", params->payload, jsonTokenStruct);
	if (jobs) {
		debug_print("inProgressJobs: %.*s", jobs->end - jobs->start, (char *)params->payload + jobs->start);
	}
	jobs = findToken("queuedJobs", params->payload, jsonTokenStruct);
	if (jobs) {
		debug_print("queuedJobs: %.*s", jobs->end - jobs->start, (char *)params->payload + jobs->start);
	}
}

/*=======================================================================================
* 函 数 名： set_flag_report_iot_update_ok
* 参    数： 
* 功能描述:  外部调用设置标志位上报固件更新成功
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-07-12 
==========================================================================================*/
void set_flag_report_iot_update_ok(int status)
{
  OTA_UPDATE_STATUS = true;//开始上报固件更新结果
  if(!status) {
    REPORT_OTA_STATUS = true;//固件更新成功
  } else {
    REPORT_OTA_STATUS = false;//上报固件更新失败
  }
}

/*=======================================================================================
* 函 数 名： aws_report_iot_update_result
* 参    数： 
* 功能描述:  上报固件更新结果
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-09-22
==========================================================================================*/
static char iotJobId[MAX_SIZE_OF_JOB_ID + 1];
static void aws_report_iot_update_result(bool status)
{
  AwsIotJobExecutionUpdateRequest updateRequest;
  IoT_Error_t rc;
	char jobId[MAX_SIZE_OF_JOB_ID + 1];
  char topicToPublishUpdate[MAX_JOB_TOPIC_LENGTH_BYTES];
  char messageBuffer[200];

  char *buf = sqlite_read_versionBak_config_db();
  //char *buf =	"49608095-8cad-4300-8f6d-aca84fca8da6";
  memcpy(jobId, buf, sizeof(jobId));
  if(status == true) {
    OTA_UPDATE_STATUS = true;
    updateRequest.status = JOB_EXECUTION_SUCCEEDED;
    updateRequest.statusDetails = "{\"exampleDetail\":\"a value appropriate for your successful job\"}";
  } else {
    OTA_UPDATE_STATUS = false;
    updateRequest.status = JOB_EXECUTION_FAILED;
    updateRequest.statusDetails = "{\"failureDetail\":\"Unable to process job document\"}";
  }
  updateRequest.expectedVersion = 0;
  updateRequest.executionNumber = 0;
  updateRequest.includeJobExecutionState = false;
  updateRequest.includeJobDocument = false;
  updateRequest.clientToken = NULL;
  //上报固件更新状态
  debug_print("aws_iot_jobs_send_update returned start \n");
  rc = aws_iot_jobs_send_update(&mqttClient, QOS0, pdev.name, jobId, &updateRequest,
    topicToPublishUpdate, sizeof(topicToPublishUpdate), messageBuffer, sizeof(messageBuffer));
  if (SUCCESS != rc) {
    debug_print("aws_iot_jobs_send_update returned error : %d \n", rc);
    return;
  }
}

/*=======================================================================================
* 函 数 名： iot_next_job_callback_handler
* 参    数： 
* 功能描述:  IOT固件更新jobs next 回调
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-07-12 
==========================================================================================*/
static void iot_next_job_callback_handler(AWS_IoT_Client *pClient, char *topicName, uint16_t topicNameLen,
									IoT_Publish_Message_Params *params, void *pData) {
	char topicToPublishUpdate[MAX_JOB_TOPIC_LENGTH_BYTES];
	char messageBuffer[200];
  char tempBuffer[512];
  char logbuf[1024];
  int status = -1;

  AwsIotJobExecutionUpdateRequest updateRequest;
  if(OTA_UPDATE_STATUS == true)
    return;
	IOT_UNUSED(pData);
	IOT_UNUSED(pClient);
	debug_print("\nJOB_NOTIFY_NEXT_TOPIC / JOB_DESCRIBE_TOPIC($next) callback\n");
  sprintf(logbuf, "%s", "JOB_NOTIFY_NEXT_TOPIC / JOB_DESCRIBE_TOPIC($next) callback");
  write_plate_write_IOT_log(logbuf);
	debug_print("topic: %.*s\n", topicNameLen, topicName);
	debug_print("payload: %.*s\n", (int)params->payloadLen, (char *)params->payload);

  sprintf(logbuf,"payload = %s",(char *)params->payload);
  write_plate_write_IOT_log(logbuf);

	jsmn_init(&jsonParser);
	tokenCount = jsmn_parse(&jsonParser, params->payload, (int) params->payloadLen, jsonTokenStruct, MAX_JSON_TOKEN_EXPECTED);
	if(tokenCount < 0) {
		debug_print("Failed to parse JSON: %d\n", tokenCount);
		return;
	}
	/* Assume the top-level element is an object */
	if(tokenCount < 1 || jsonTokenStruct[0].type != JSMN_OBJECT) {
		debug_print("Top Level is not an object\n");
		return;
	}

	jsmntok_t *tokExecution;
	tokExecution = findToken("execution", params->payload, jsonTokenStruct);
	if (tokExecution) {
		debug_print("execution: %.*s\n", tokExecution->end - tokExecution->start, (char *)params->payload + tokExecution->start);
		jsmntok_t *tok;
		tok = findToken("jobId", params->payload, tokExecution);
		if (tok) {
			IoT_Error_t rc;
			char jobId[MAX_SIZE_OF_JOB_ID + 1];
			
			rc = parseStringValue(jobId, MAX_SIZE_OF_JOB_ID + 1, params->payload, tok);
			if(SUCCESS != rc) {
				debug_print("parseStringValue returned error : %d \n", rc);
				return;
			}
			debug_print("jobId: %s \n", jobId);
			tok = findToken("jobDocument", params->payload, tokExecution);

			/* Do your job processing here.*/
			if (tok) {
				debug_print("jobDocument: %.*s\n", tok->end - tok->start, (char *)params->payload + tok->start);
        memset(tempBuffer, 0, 512);
        memcpy(tempBuffer, (char *)params->payload + tok->start+1, tok->end - tok->start - 2);
        debug_print("tempBuffer = %s\n", tempBuffer);
        //json 解析出下载的url地址
        cJSON * root = NULL;
        cJSON * item = NULL;//cjson对象   
        root = cJSON_Parse(tempBuffer);     
        if (!root) {
          printf("Error before: [%s]\n",cJSON_GetErrorPtr());
        } else {
          item = cJSON_GetObjectItem(root, "downloadPath");
          char * downUrl = cJSON_Print(item);
          memset(tempBuffer, 0, 512);
          memcpy(tempBuffer, downUrl+1 ,strlen(downUrl)-2);
          debug_print("downloadPath = %s\n", tempBuffer);
          status = aws_ota_handler(tempBuffer);//从AWS 3s地址下载新的固件
          debug_print("固件更新状态 = %d\n", status);
        }
        cJSON_Delete(root);
        if (!status ) {//固件更新成功 
          /* Alternatively if the job still has more steps the status can be set to JOB_EXECUTION_IN_PROGRESS instead */
          // OTA_UPDATE_STATUS = true;
          // updateRequest.status = JOB_EXECUTION_SUCCEEDED;
          // updateRequest.statusDetails = "{\"exampleDetail\":\"a value appropriate for your successful job\"}";
          //清空进程保护数据库
          sqlite_update_process_protection_db_null();
          //读取软件版本号写入配置数据库临时软件版本字段
          if(sqlite_update_versionBak_config_db(jobId) == 0xff) {//已是最新版本直接回复IOT固件更新成功
            OTA_UPDATE_STATUS = true;
            updateRequest.status = JOB_EXECUTION_SUCCEEDED;
            updateRequest.statusDetails = "{\"exampleDetail\":\"a value appropriate for your successful job\"}";
          } else {
            system("/home/meican/ota/run.sh"); //运行固件包里面的脚本文件 
            return;
          } 
        } else {//固件更新失败
          OTA_UPDATE_STATUS = false;
          updateRequest.status = JOB_EXECUTION_FAILED;
				  updateRequest.statusDetails = "{\"failureDetail\":\"Unable to process job document\"}";
        }
			} else {//固件更新失败
        OTA_UPDATE_STATUS = false;
				updateRequest.status = JOB_EXECUTION_FAILED;
				updateRequest.statusDetails = "{\"failureDetail\":\"Unable to process job document\"}";
			}
			updateRequest.expectedVersion = 0;
			updateRequest.executionNumber = 0;
			updateRequest.includeJobExecutionState = false;
			updateRequest.includeJobDocument = false;
			updateRequest.clientToken = NULL;
      //上报固件更新状态
      debug_print("aws_iot_jobs_send_update returned start \n");
			rc = aws_iot_jobs_send_update(pClient, QOS0, pdev.name, jobId, &updateRequest,
				topicToPublishUpdate, sizeof(topicToPublishUpdate), messageBuffer, sizeof(messageBuffer));
			if (SUCCESS != rc) {
				debug_print("aws_iot_jobs_send_update returned error : %d \n", rc);
				return;
			}
		}
	} else {
		debug_print("execution property not found, nothing to do\n");
	}
}

/*=======================================================================================
* 函 数 名： iot_update_accepted_callback_handler
* 参    数： 
* 功能描述:  jobs固件更新update 上报回调
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-30 
==========================================================================================*/
static void iot_update_accepted_callback_handler(AWS_IoT_Client *pClient, char *topicName, uint16_t topicNameLen,
									IoT_Publish_Message_Params *params, void *pData) {
  char logbuf[100];
  char sendbuf[20];
  char ver[100];

	IOT_UNUSED(pData);
	IOT_UNUSED(pClient);
	debug_print("JOB_UPDATE_TOPIC / accepted callback\n");
  sprintf(logbuf,"%s","JOB_UPDATE_TOPIC / accepted callback");
  write_plate_write_IOT_log(logbuf);
	debug_print("topic: %.*s\n", topicNameLen, topicName);
	debug_print("payload: %.*s\n", (int)params->payloadLen, (char *)params->payload);
  if(OTA_UPDATE_STATUS == true) {//固件更新成功
    OTA_UPDATE_STATUS = false;
    debug_print("固件更新成功停止上报");

    memset(ver,0,100);
    //从软件版本txt读取软件版本
    read_version_from_txt(ver);
    debug_print("version = %s \n", ver);
    sqlite_update_version_config_db(ver); //读取软件版本号写入配置数据库
    //reboot_qt_app();
    // system("kill -9 $(pidof WriteDisk)"); //重新运行QT程序
    // system("/home/meican/WriteDisk"); //重新运行QT程序
    // sqlite_update_versionBak_config_db();//读取软件版本号写入配置数据库临时软件版本字段
    // system("/home/meican/ota/run.sh"); //运行固件包里面的脚本文件
    //发送固件更新成功命令到QT
		aws_send_ota_update_to_qt(1, 100);

    //从配置数据库读取设备信息
    devMsg = sqlite_read_devMsg_from_config_db();
    reportromVersionFlag = true;//上报新的固件版本
  }
}

static void iot_update_rejected_callback_handler(AWS_IoT_Client *pClient, char *topicName, uint16_t topicNameLen,
									IoT_Publish_Message_Params *params, void *pData) {
	IOT_UNUSED(pData);
	IOT_UNUSED(pClient);
	debug_print("\nJOB_UPDATE_TOPIC / rejected callback\n");
	debug_print("topic: %.*s\n", topicNameLen, topicName);
	debug_print("payload: %.*s\n", (int) params->payloadLen, (char *)params->payload);
  if(OTA_UPDATE_STATUS == true) {//固件更新成功
    OTA_UPDATE_STATUS = false;
  }
	/* Do error handling here for when the update was rejected */
}

/*=======================================================================================
* 函 数 名： aws_send_data_to_qt
* 参    数： 
* 功能描述:  消息队列发送数据到QT
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-30 
==========================================================================================*/
static void aws_send_data_to_qt(int cmd, uint8_t *data, int len) 
{
  qtdata_t mSndMsg;

  mSndMsg.datalen = len+2;
  mSndMsg.cmd = cmd;
  memcpy(mSndMsg.data, data, len);
  send_data_to_qt_direct(mSndMsg);//发送设备状态到QT
}

/*=======================================================================================
* 函 数 名： aws_send_change_status_to_qt
* 参    数： 
* 功能描述:  消息队列发送更改设备状态
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-30 
==========================================================================================*/
void aws_send_change_status_to_qt(int status) 
{
  qtdata_t mSndMsg;

  mSndMsg.datalen = 3;
  mSndMsg.cmd = WRPLATE_DEV_STATUS_CMD;
  mSndMsg.data[0] = status;
  send_data_to_qt_direct(mSndMsg);//发送设备状态到QT
}

/*=======================================================================================
* 函 数 名： aws_send_data_to_qt
* 参    数： status==更新状态；progress==更新进度
* 功能描述:  消息队列发送菜单获取状态
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-30 
==========================================================================================*/
void aws_send_menu_status_to_qt(int status, int progress) 
{
  qtdata_t mSndMsg;

  mSndMsg.datalen = 4;
  mSndMsg.cmd = WRPLATE_MENU_STATUS_CMD;
  mSndMsg.data[0] = status;
  mSndMsg.data[1] = progress;
  send_data_to_qt_direct(mSndMsg);//发送设备状态到QT
}

/*=======================================================================================
* 函 数 名： aws_send_ota_update_to_qt
* 参    数： status==更新状态；progress==更新进度
* 功能描述:  消息队列发送固件更新状态
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-30 
==========================================================================================*/
void aws_send_ota_update_to_qt(int status, int progress) 
{
  qtdata_t mSndMsg;

  mSndMsg.datalen = 4;
  mSndMsg.cmd = WRPLATE_OTA_UPDATE_CMD;
  mSndMsg.data[0] = status;
  mSndMsg.data[1] = progress;
  send_data_to_qt_direct(mSndMsg);//发送设备状态到QT
}

/*=======================================================================================
* 函 数 名： clear_menu_db
* 参    数： 
* 功能描述:  解绑； 清空菜单数据库； 创建基础菜单数据库
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-30 
==========================================================================================*/
static void unbind_clear_menu_db(void) 
{
  uint8_t sendbuf[20];
  C_menuMsgSt pmenuSt;

  //解绑完成； 修改配置数据库设备状态为解绑状态（出厂状态）
  devMsg.status = C_FACTORY_BIND_OK_STATUS ;   
  while(sqlite_update_dev_status_config_db(devMsg.status)) {
    reboot_golang();
  }
  //清除餐厅ID
  sqlite_update_dev_restaurantId_config_db(0);
  //配置数据库菜单版本信息归 0
  pmenuSt.menu_level = 0;
  pmenuSt.menu_ver = 0; //菜单版本
  pmenuSt.new_menu_ver = 0;
  while(sqlite_update_menuMsg_to_config_db(pmenuSt)) {
    reboot_golang();
  }
  //删除菜单数据库
  //system("find -name \"/home/meican/menudb/menu*\" | xargs rm -rfv");
  system("rm -rf /home/meican/menudb");
  sleep(1);
  system("mkdir /home/meican/menudb" );
  sleep(1);
  //创建菜单基础数据库
  sqlite_create_menu_db("menu_lev1");
  //发送解绑指令到QT
  sendbuf[0] = C_FACTORY_BIND_OK_STATUS;
  aws_send_data_to_qt(WRPLATE_DEV_STATUS_CMD,sendbuf,1);
}

/**
 * @brief This function builds a full Shadow expected JSON document by putting the data in the reported section
 *
 * @param pJsonDocument Buffer to be filled up with the JSON data
 * @param maxSizeOfJsonDocument maximum size of the buffer that could be used to fill
 * @param pReceivedDeltaData This is the data that will be embedded in the reported section of the JSON document
 * @param lengthDelta Length of the data
 */
static bool buildJSONForReported(char *pJsonDocument, size_t maxSizeOfJsonDocument, const char *pReceivedDeltaData, uint32_t lengthDelta) 
{
	int32_t ret;

	if (NULL == pJsonDocument) {
		return false;
	}
	char tempClientTokenBuffer[MAX_SIZE_CLIENT_TOKEN_CLIENT_SEQUENCE];
	if(aws_iot_fill_with_client_token(tempClientTokenBuffer, MAX_SIZE_CLIENT_TOKEN_CLIENT_SEQUENCE) != SUCCESS) {
		return false;
	}
	ret = snprintf(pJsonDocument, maxSizeOfJsonDocument, "{\"state\":{\"reported\":%.*s}, \"clientToken\":\"%s\"}", 
                lengthDelta, pReceivedDeltaData, tempClientTokenBuffer);
	if (ret >= maxSizeOfJsonDocument || ret < 0) {
		return false;
	}
	return true;
}

//***************CJSON*********************// parseCMDJSON create_monitor_with_helpers用于解析或构造state内容
static int parsePloadJSON(const char * const monitor) 
{//使用CJSON解析get shadow返回的消息
    const cJSON *state = NULL;
    const cJSON *desired = NULL;
    const cJSON *restaurantIDJson = NULL;
    const cJSON *menuUpdateTime = NULL;
    const cJSON *romVersion = NULL;
    const cJSON *sn = NULL;
    const cJSON *snJson = NULL;
    const cJSON *codeJson = NULL;
    int status = 0;

    memset(devSn,0,100);
    memset(code,0,100);

    cJSON *monitor_json = cJSON_Parse(monitor);//它将解析JSON并分配cJSON表示它的项目树。
    if (monitor_json == NULL) {
        const char *error_ptr = cJSON_GetErrorPtr();
        if (error_ptr != NULL) {
          fprintf(stderr, "Error before: %s\n", error_ptr);
        }
        status = 0;
        goto end;
    }
    state = cJSON_GetObjectItemCaseSensitive(monitor_json, "state");//得到state内容
    if (cJSON_IsString(state) && (state->valuestring != NULL)) {
      printf("Checking monitor \"%s\"\n", state->valuestring);
    }

    desired = cJSON_GetObjectItemCaseSensitive(state, "desired");//从stated尝试解析desired
    if (!cJSON_IsNull(desired)) {//如果desired不为空，所以应该用desired状态同步本状态。上面reported同步的状态将被覆盖
      restaurantIDJson = cJSON_GetObjectItemCaseSensitive(desired, "restaurantID");
      menuUpdateTime = cJSON_GetObjectItemCaseSensitive(desired, "menuUpdateTime");
      romVersion =  cJSON_GetObjectItemCaseSensitive(desired, "romVersion");
      sn = cJSON_GetObjectItemCaseSensitive(desired, "sn");

      if (cJSON_IsNumber(restaurantIDJson)) { //获取餐厅ID
        debug_print("restaurantIDJson = %d\n", restaurantIDJson->valueint);
        if (!(restaurantIDJson->valueint)) {//设备已经解绑
          unbind_clear_menu_db();//解绑；清空菜单数据库；并创建基础菜单数据库
          restaurantID = 0;//上报 restaurantID = 0 到 IOT 
          reportRestaurantIDFlag = true;//上报餐厅ID 到 IOT
        }
      }
      if (cJSON_IsNumber(menuUpdateTime)) { //获取后台菜单版本
        char *strbuf = cJSON_Print(menuUpdateTime);
        debug_print("menuUpdateTime = %lld\n", atoll(strbuf));
        debug_print("cmenuMsg.new_menu_ver = %lld\n", cmenuMsg.new_menu_ver);
        if (cmenuMsg.new_menu_ver < atoll(strbuf)) {//后台菜单版本 > 当前菜单版本
          debug_print("菜单需要更新\n");
          cmenuMsg.new_menu_ver = atoll(strbuf);
          free(strbuf);
          //更新需要更新的菜单版本信息
          while(sqlite_update_menuMsg_to_config_db(cmenuMsg)) {
            reboot_golang();
          }
        }
      }
      if (cJSON_IsString(romVersion)) { //获取固件版本
        debug_print("romVersion = %s\n", romVersion->valuestring);
      }
      if (cJSON_IsObject(sn)) {
        char *snbuf = cJSON_Print(sn);
        debug_print("snJson = %s\n", snbuf);
        free(snbuf);
        snJson = cJSON_GetObjectItemCaseSensitive(sn, "sn");
        if (cJSON_IsString(snJson)) { 
          debug_print("sn = %s\n", snJson->valuestring); 
          if (memcmp(devSn,snJson->valuestring,strlen(snJson->valuestring))) {
            debug_print("sn 需要更新\n");
            memcpy(devSn,snJson->valuestring,strlen(snJson->valuestring)); 
            while(sqlite_update_dev_sn_config_db(devSn,code)) {
              reboot_golang();
            }//修改配置数据库sn码,v2id(六位数字用于二维码显示)
          }     
        }
        codeJson = cJSON_GetObjectItemCaseSensitive(sn, "code");
        if (cJSON_IsString(codeJson)) { 
          debug_print("code = %s\n", codeJson->valuestring);
          if (memcmp(code,codeJson->valuestring,strlen(codeJson->valuestring))) {
            debug_print("code 需要更新\n");
            memcpy(code,codeJson->valuestring,strlen(codeJson->valuestring));  
            while(sqlite_update_dev_sn_config_db(devSn,code)) {
              reboot_golang();
            }//修改配置数据库sn码,v2id(六位数字用于二维码显示)
            if(devMsg.status < C_FACTORY_BIND_OK_STATUS)
            {
              devMsg.status = C_FACTORY_BIND_OK_STATUS;
              sqlite_update_dev_status_config_db(devMsg.status);//修改配置数据库设备状态
              system("/home/meican/rebootQt.sh");//
            }
          }   
        }
      }
      status = 1;
    }
end:
    cJSON_Delete(monitor_json);
    return status;
}

/*=======================================================================================
* 函 数 名： disconnectCallbackHandler
* 参    数： 
* 功能描述:  AWS IOT 连接状态回调
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
static void disconnectCallbackHandler(AWS_IoT_Client *pClient, void *data) {
  qtdata_t mSndMsg;
  uint8_t sendbuf[20];
  char logbuf[200];
	IoT_Error_t rc = FAILURE;

  debug_print("MQTT Disconnect start\n");
	if(NULL == pClient) {
		return;
	}
  sprintf(logbuf,"%s","MQTT Disconnect");
  write_plate_write_IOT_log(logbuf);
  debug_print("MQTT Disconnect \n");
  getShadowFlag = true;//网络断开使能定时获取shadow状态任务
  //发送断网指令到QT
  sendbuf[0] = NETWORK_DISCONNECT;
  aws_send_data_to_qt(WRPLATE_NET_STATUS_CMD,sendbuf,1);

	IOT_UNUSED(data);
	if(aws_iot_is_autoreconnect_enabled(pClient)) {
		debug_print("Auto Reconnect is enabled, Reconnecting attempt will start now\n");
	} else {
		debug_print("Auto Reconnect not enabled. Starting manual reconnect...\n");
		rc = aws_iot_mqtt_attempt_reconnect(pClient);
		if(NETWORK_RECONNECTED == rc) {
			debug_print("Manual Reconnect Successful\n");
		} else {
			debug_print("Manual Reconnect Failed - %d\n", rc);
		}
	}
}

/*=======================================================================================
* 函 数 名： GetShadowStatusCallback
* 参    数： 
* 功能描述:  get shadow 回调
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
static void GetShadowStatusCallback(const char *pThingName, ShadowActions_t action, Shadow_Ack_Status_t status,
								const char *pReceivedJsonDocument, void *pContextData) 
{
  char logbuf[2048];
  uint8_t sendbuf[20];
  qtdata_t mSndMsg;
  IoT_Error_t rc = FAILURE;
  IoT_Publish_Message_Params paramsQOS0;

  iot_connect_status_bak = CLIENT_STATE_CONNECTED_IDLE;
  IOT_UNUSED(pThingName);
	IOT_UNUSED(action);
	IOT_UNUSED(pReceivedJsonDocument);
	IOT_UNUSED(pContextData);
	debug_print("shadow pReceivedJsonDocument 数据 = %s \n",pReceivedJsonDocument);
  sprintf(logbuf,"shadow pReceivedJsonDocument 数据 = %s",pReceivedJsonDocument);
  write_plate_write_IOT_log(logbuf);
  debug_print("shadow status = %d \n",status);
	if(status != SHADOW_ACK_TIMEOUT) {
    getShadowFlag = false;//获取成功停止获取
		//strcpy(jsonFullDocument, pReceivedJsonDocument);
    parsePloadJSON(pReceivedJsonDocument);
    //发送IOT联网成功指令到QT
    sendbuf[0] = IOT_CONNECT_OK;
    aws_send_data_to_qt(WRPLATE_NET_STATUS_CMD,sendbuf,1);
    reportromVersionFlag = true;//开机连到IOT获取到当前shadow状态后后上报固件版本
    reportmenuUpdateTimeFlag = true;//开机连到IOT后上报当前的菜单版本
	} else {
    debug_print("get shadow time out !! \n");
    getShadowFlag = true;//get shadow 失败继续获取
  }
}

/*=======================================================================================
* 函 数 名： ShadowMenuUpdateTimeUpdateStatusCallback
* 参    数： 
* 功能描述:  menuUpdateTime更新状态回调
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
static void ShadowMenuUpdateTimeUpdateStatusCallback(const char *pThingName, ShadowActions_t action, 
                      Shadow_Ack_Status_t status,const char *pReceivedJsonDocument, void *pContextData) 
{
  char logbuf[100];
	IOT_UNUSED(pThingName);
	IOT_UNUSED(action);
	IOT_UNUSED(pReceivedJsonDocument);
	IOT_UNUSED(pContextData);

	if(SHADOW_ACK_ACCEPTED == status) {
    reportmenuUpdateTimeFlag = false;//上报成功，停止上报
		debug_print("MenuUpdateTime Update Accepted !!\n");
    sprintf(logbuf,"%s","MenuUpdateTime Update Accepted !!");
    write_plate_write_IOT_log(logbuf);
	} else {
    reportmenuUpdateTimeFlag = true;//上报失败，继续上报
  }
}

/*=======================================================================================
* 函 数 名： ShadowMenuUpdateRomVersionStatusCallback
* 参    数： 
* 功能描述:  romVersion更新状态回调
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-30 
==========================================================================================*/
static void ShadowMenuUpdateRomVersionStatusCallback(const char *pThingName, ShadowActions_t action, 
                      Shadow_Ack_Status_t status, const char *pReceivedJsonDocument, void *pContextData) 
{
  char logbuf[100];
	IOT_UNUSED(pThingName);
	IOT_UNUSED(action);
	IOT_UNUSED(pReceivedJsonDocument);
	IOT_UNUSED(pContextData);

	if(SHADOW_ACK_ACCEPTED == status) {
    reportromVersionFlag = false;//上报成功，停止上报
		debug_print("romVersion Update Accepted !!\n");
    sprintf(logbuf,"%s","romVersion Update Accepted !!");
    write_plate_write_IOT_log(logbuf);
	} else {
    reportromVersionFlag = true;//上报失败，继续上报
  }
}

/*=======================================================================================
* 函 数 名： ShadowRestaurantIDUpdateStatusCallback
* 参    数： 
* 功能描述:  restaurantID更新状态回调
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
static void ShadowRestaurantIDUpdateStatusCallback(const char *pThingName, ShadowActions_t action, 
                  Shadow_Ack_Status_t status, const char *pReceivedJsonDocument, void *pContextData) 
{
  char logbuf[100];
  uint8_t sendbuf[20];
  qtdata_t mSndMsg;

	IOT_UNUSED(pThingName);
	IOT_UNUSED(action);
	IOT_UNUSED(pReceivedJsonDocument);
	IOT_UNUSED(pContextData);

  if(SHADOW_ACK_ACCEPTED == status) {
    reportRestaurantIDFlag = false;//上报成功，停止上报
    
    debug_print("食堂Id = %d\n",restaurantID);
    if(restaurantID) {//绑定
      debug_print("现场食堂绑定完成 \n");
      devMsg.status = C_SITE_BIND_OK_STATUS ;   //现场绑定完成，可以正常写盘拉菜单
      while(sqlite_update_dev_status_config_db(devMsg.status))//修改配置数据库设备状态为食堂绑定完成可以正常工作
      {
        reboot_golang();
      }
      //发送绑定食堂指令到QT
      sendbuf[0] = C_SITE_BIND_OK_STATUS;
      aws_send_data_to_qt(WRPLATE_DEV_STATUS_CMD,sendbuf,1);
    } else {//解绑
      //发送解绑指令到QT
      sendbuf[0] = C_FACTORY_BIND_OK_STATUS;
      aws_send_data_to_qt(WRPLATE_DEV_STATUS_CMD,sendbuf,1);
      debug_print("解绑完成 \n");
    }
		debug_print("restaurantID Update Accepted !!\n");
    sprintf(logbuf,"%s","restaurantID Update Accepted !!");
    write_plate_write_IOT_log(logbuf);
	} else {
    reportRestaurantIDFlag = true;//上报失败继续上报
  }
}

/*=======================================================================================
* 函 数 名： ShadowUpdateStatusCallback
* 参    数： 
* 功能描述:  sn更新状态回调
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
static void ShadowSnUpdateStatusCallback(const char *pThingName, ShadowActions_t action, Shadow_Ack_Status_t status,
								const char *pReceivedJsonDocument, void *pContextData) 
{
  uint8_t sendbuf[20];
  char logbuf[100];
  qtdata_t mSndMsg;

	IOT_UNUSED(pThingName);
	IOT_UNUSED(action);
	IOT_UNUSED(pReceivedJsonDocument);
	IOT_UNUSED(pContextData);

  if(SHADOW_ACK_ACCEPTED == status) {
    reportSnFlag = false;//上报成功，停止上报
    if(devMsg.status == C_WAIT_TOPIC_STATUS ) {
      devMsg.status = C_FACTORY_BIND_OK_STATUS;//设备状态更改为工厂绑定完成状态
      while(sqlite_update_dev_status_config_db(devMsg.status))//修改配置数据库设备状态
      {
        reboot_golang();
      }
      //发送出厂绑定指令到QT
      sendbuf[0] = C_FACTORY_BIND_OK_STATUS;
      aws_send_data_to_qt(WRPLATE_DEV_STATUS_CMD,sendbuf,1);
    }
    if(strlen(devSn)==0&strlen(code)==0) {//SN解绑重启设备
        devMsg.status = C_WAIT_TOPIC_STATUS;//设备状态更改为工厂绑定完成状态
        while(sqlite_update_dev_status_config_db(devMsg.status))//修改配置数据库设备状态
        debug_print("sn解绑完成，设备重启\n");
        sleep(3); 
        system("reboot");
    } 
		debug_print("sn Update Accepted !!\n");
    sprintf(logbuf,"%s","sn Update Accepted !!");
    write_plate_write_IOT_log(logbuf);
	} else {
    reportSnFlag = true;//report失败，继续上报
  }
}

/*=======================================================================================
* 函 数 名： menuUpdateTime_Callback
* 参    数： 
* 功能描述:  写盘器菜单更新回调函数
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
static void menuUpdateTime_Callback(const char *pJsonString, uint32_t JsonStringDataLen, jsonStruct_t *pContext) 
{
  char logbuf[100];
  char sendbuf[10];
	IOT_UNUSED(pJsonString);
	IOT_UNUSED(JsonStringDataLen);

	if(pContext != NULL) {
		debug_print("Delta - menuUpdateTime state changed to %lld\n", *(int64_t *)(pContext->pData));	
    sprintf(logbuf,"Delta - menuUpdateTime state changed to = %lld",*(int64_t *)(pContext->pData));
    write_plate_write_IOT_log(logbuf);

    if(*(int64_t *)(pContext->pData) >  cmenuMsg.new_menu_ver) {
      cmenuMsg.new_menu_ver =  *(int64_t *)(pContext->pData);
      menuUpdateTime = cmenuMsg.new_menu_ver;
      //更新需要更新的菜单版本信息
      while(sqlite_update_menuMsg_to_config_db(cmenuMsg)) {
        reboot_golang();
      }
      //发送菜单开始更新消息队列到QT
      // sendbuf[0] = 0;
      // aws_send_data_to_qt(WRPLATE_MENU_STATUS_CMD,sendbuf,1);
      set_stop_write_palte_status(); //菜单更新时停止写盘

      debug_print("current.menu_ver = %lld \n",cmenuMsg.menu_ver );
      debug_print("new_menu_ver = %lld \n",cmenuMsg.new_menu_ver);
    } else {
      //cmenuMsg = sqlite_read_menuMsg_from_config_db();
      menuUpdateTime = cmenuMsg.new_menu_ver;
      debug_print("已是最新版本");
      reportmenuUpdateTimeFlag = true;//上报已是最新版本
    }
	}
}

/*=======================================================================================
* 函 数 名： restaurantID_Callback
* 参    数： 
* 功能描述:  restaurantID更新回调函数
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
static void restaurantID_Callback(const char *pJsonString, uint32_t JsonStringDataLen, jsonStruct_t *pContext) 
{
  char logbuf[100];
	IOT_UNUSED(pJsonString);
	IOT_UNUSED(JsonStringDataLen);

	if(pContext != NULL) {
    restaurantID = *(int64_t *)(pContext->pData);
		debug_print("Delta - restaurantID state changed to %lld\n", restaurantID);
    // sprintf(logbuf,"Received Delta message = %lld",restaurantID);
    // write_plate_write_IOT_log(logbuf);
    //修改配置数据库餐厅识别码
    while(sqlite_update_dev_restaurantId_config_db(restaurantID)) {
      reboot_golang();
    }  
    //如果 restaurantID = 0；后台解绑；写盘器配置数据库设备状态改为出厂状态(2)
    if(restaurantID == 0) {
      unbind_clear_menu_db();//解绑；清空菜单数据库；并创建基础菜单数据库
    }
    //上报餐厅id
    reportRestaurantIDFlag = true;	  
	}
}

/*=======================================================================================
* 函 数 名： snUpdate_Callback
* 参    数： 
* 功能描述:  写盘器SN更新回调函数
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
static void sn_Callback(const char *pJsonValueBuffer, uint32_t valueLength, jsonStruct_t *pContext) 
{
	IoT_Error_t rc = SUCCESS;
	int dev_Status =-1;
  int err,v2vid;
  char temp[100];
  char logbuf[200];
  uint8_t sendbuf[20];
  qtdata_t mSndMsg;

	IOT_UNUSED(pContext);

  if(pContext == NULL) {
    return;
  }
	debug_print("Received Delta message %.*s \n", valueLength, pJsonValueBuffer);
  // sprintf(logbuf,"Received Delta message = %s",pJsonValueBuffer);
  // write_plate_write_IOT_log(logbuf);

	//解析JSON数据
  cJSON *root_json = cJSON_Parse(pJsonValueBuffer);    //将字符串解析成json结构体
  if (NULL == root_json) {
    debug_print("error:%s\n", cJSON_GetErrorPtr());
    cJSON_Delete(root_json);
    return;
  }
  //json解析 sn  code
  cJSON *name_json = cJSON_GetObjectItem(root_json, "sn");
  cJSON *code_json = cJSON_GetObjectItem(root_json, "code");
  if (name_json != NULL) {
    char *name = cJSON_Print(name_json);    //将JSON结构体打印到字符串中 需要自己释放
    del_char(name,'\"');//去掉字符串里面的“ “ ”
    memset(devSn,0,100);
    memset(code,0,100);
    if(strcmp(devSn,name)) 
    { 
      memcpy(devSn,name,strlen(name));    
      if (code_json != NULL) {
        char *name1 = cJSON_Print(code_json);    //将JSON结构体打印到字符串中 需要自己释放
        del_char(name1,'\"');//去掉字符串里面的“ “ ”
        memcpy(code,name1,strlen(name1));  
        free(name1);
      }
      debug_print("sn = %s\n", devSn); 
      debug_print("code = %s \n",code);
      make_mctid_barcode(devSn);//创建sn码条形码
      
      while(sqlite_update_dev_sn_config_db(devSn,code)) {
        reboot_golang();
      }//修改配置数据库sn码,v2id(六位数字用于二维码显示)
      //发送id到QT用于二维码显示
      v2vid = atoi(code);
      memcpy(sendbuf,&v2vid,4);
      
    } else {//sn 码为空，接触设备绑定回到二维码界面
      char *name = cJSON_Print(name_json);    //将JSON结构体打印到字符串中 需要自己释放
      del_char(name,'\"');//去掉字符串里面的“ “ ”
      memcpy(devSn,name,strlen(name));  
      char *name1 = cJSON_Print(code_json);    //将JSON结构体打印到字符串中 需要自己释放
      del_char(name1,'\"');//去掉字符串里面的“ “ ”
      memcpy(code,name1,strlen(name1));  
      
      debug_print("null sn = %s\n", devSn); 
      debug_print("null code = %s \n",code);
      if(strlen(name) ==0 && strlen(name1) == 0) {
        printf("code为空,sn为空，回到二维码界面\n");
        while(sqlite_update_dev_sn_config_db(devSn,code)) {
          devMsg.status = C_WAIT_TOPIC_STATUS;
          sqlite_update_dev_status_config_db(devMsg.status);//修改配置数据库设备状态
          // reboot_qt();
          // reboot_golang();
         // system("reboot");
        }//修改配置数据库sn码,v2id(六位数字用于二维码显示)
      }
      free(name);
      free(name1);
  }
    free(name);
  } 
  
  reportSnFlag = true;//开始上报sn
  cJSON_Delete(root_json); 
}

/*=======================================================================================
* 函 数 名： get_aws_iot_dev_status
* 参    数： 
* 功能描述:  返回当前的设备状态
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
int  get_aws_iot_dev_status(void) 
{
  return devMsg.status;
}

/*=======================================================================================
* 函 数 名： update_aws_iot_dev_status
* 参    数： 
* 功能描述:  更改设备状态
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
void  update_aws_iot_dev_status(int status) 
{
  uint8_t sendbuf[20];

  devMsg.status = status;
  sendbuf[0] = devMsg.status;
  aws_send_data_to_qt(WRPLATE_DEV_STATUS_CMD,sendbuf,1);//发送更改后的设备状态到QT
}

/*=======================================================================================
* 函 数 名： set_aws_iot_report_menuUpdateTime
* 参    数： 
* 功能描述:  设置iot 上报菜单已更新完成
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
void  set_aws_iot_report_menuUpdateTime(void) 
{
  reportmenuUpdateTimeFlag = true;
}

/*=======================================================================================
* 函 数 名： set_aws_iot_report_romVersion
* 参    数： 
* 功能描述:  设置iot 上报固件版本
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
void  set_aws_iot_report_romVersion(void) 
{
  reportromVersionFlag = true;//开机连到IOT获取到当前shadow状态后后上报固件版本
}

/*=======================================================================================
* 函 数 名： write_plate_aws_iot_shadow_init
* 参    数： 
* 功能描述:  写盘器AWS IOT SHADOW 初始化
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
IoT_Error_t   write_plate_aws_iot_shadow_init(void) 
{
  IoT_Error_t rc = FAILURE;
  char topicToSubscribeGetPending[MAX_JOB_TOPIC_LENGTH_BYTES];
	char topicToSubscribeNotifyNext[MAX_JOB_TOPIC_LENGTH_BYTES];
	char topicToSubscribeGetNext[MAX_JOB_TOPIC_LENGTH_BYTES];
	char topicToSubscribeUpdateAccepted[MAX_JOB_TOPIC_LENGTH_BYTES];
	char topicToSubscribeUpdateRejected[MAX_JOB_TOPIC_LENGTH_BYTES];

	char topicToPublishGetPending[MAX_JOB_TOPIC_LENGTH_BYTES];
	char topicToPublishGetNext[MAX_JOB_TOPIC_LENGTH_BYTES];
  char cPayload[100];
  char shadow_name[100];
  char shadow_id[100];
  char logbuf[200];
  IoT_Publish_Message_Params paramsQOS0;

  //从配置数据库获取ThingName，ClientId
  pdev = sqlite_read_shandow_config_message();
  memcpy(shadow_name,pdev.name,strlen(pdev.name));
  memcpy(shadow_id,pdev.clientid,strlen(pdev.clientid));
  debug_print("pdev.name = %s \n",pdev.name);
  debug_print("pdev.clientid = %s \n",pdev.clientid);
  //从配置数据库读取菜单版本
  cmenuMsg = sqlite_read_menuMsg_from_config_db();
  debug_print("current.menu_ver = %lld \n",cmenuMsg.menu_ver );
  debug_print("new_menu_ver = %lld \n",cmenuMsg.new_menu_ver);
  menuUpdateTime = cmenuMsg.menu_ver;
  //从配置数据库读取设备信息
  devMsg = sqlite_read_devMsg_from_config_db();
  memcpy(devSn,devMsg.sn,strlen(devMsg.sn));
  sprintf(code,"%d",devMsg.id);
  debug_print("devSn = %s \n",devSn);
  debug_print("code = %s \n",code);
  devMsg.status = sqlite_read_device_satus();
  debug_print("devMsg.status = %d \n",devMsg.status);
  debug_print("devMsg.version = %d \n",devMsg.version);

  //菜单更新时间，Unix timestamp (毫秒)
	menuUpdateTimeHandler.cb = menuUpdateTime_Callback;
	menuUpdateTimeHandler.pData = &menuUpdateTime;
	menuUpdateTimeHandler.dataLength = sizeof(int64_t);
	menuUpdateTimeHandler.pKey = "menuUpdateTime";
	menuUpdateTimeHandler.type = SHADOW_JSON_INT64;

	//绑定的餐厅 ID，0 表示未绑定餐厅
	restaurantIDHandler.cb = restaurantID_Callback;
	restaurantIDHandler.pKey = "restaurantID";
	restaurantIDHandler.pData = &restaurantID;
	restaurantIDHandler.dataLength = sizeof(int64_t);
	restaurantIDHandler.type = SHADOW_JSON_INT64;

	//SN码字段
	snHandler.cb = sn_Callback;
	snHandler.pKey = "sn";
	snHandler.pData = snDeltaData;
	snHandler.dataLength = SHADOW_MAX_SIZE_OF_RX_BUFFER;
	snHandler.type = SHADOW_JSON_OBJECT;

  //固件版本字段
	versionHandler.cb = NULL;
	versionHandler.pKey = "romVersion";
	versionHandler.pData = version;
	versionHandler.dataLength = SHADOW_MAX_SIZE_OF_RX_BUFFER;
	versionHandler.type = SHADOW_JSON_STRING;

	char rootCA[PATH_MAX + 1];
	char clientCRT[PATH_MAX + 1];
	char clientKey[PATH_MAX + 1];
	char CurrentWD[PATH_MAX + 1] = "";

	debug_print("\nAWS IoT SDK Version %d.%d.%d-%s\n", VERSION_MAJOR, VERSION_MINOR, VERSION_PATCH, VERSION_TAG);

	debug_print("rootCA %s\n", rootCA);
	debug_print("clientCRT %s\n", clientCRT);
	debug_print("clientKey %s\n", clientKey);

	// generate the paths of the credentials
	getcwd(CurrentWD, sizeof(CurrentWD));

	snprintf(rootCA,    PATH_MAX + 1, "%s/%s/%s", "/home/meican", certDirectory, AWS_IOT_ROOT_CA_FILENAME);
	snprintf(clientCRT, PATH_MAX + 1, "%s/%s/%s", "/home/meican", certDirectory, AWS_IOT_CERTIFICATE_FILENAME);
	snprintf(clientKey, PATH_MAX + 1, "%s/%s/%s", "/home/meican", certDirectory, AWS_IOT_PRIVATE_KEY_FILENAME);
	debug_print("CurrentWD = %s \n",CurrentWD);
	debug_print("rootCA    = %s \n",rootCA);
	debug_print("clientCRT = %s \n",clientCRT);
	debug_print("clientKey = %s \n",clientKey);

	sp = ShadowInitParametersDefault;
	sp.pHost = HostAddress;
	sp.port = port;
	sp.pClientCRT = clientCRT;
	sp.pClientKey = clientKey;
	sp.pRootCA = rootCA;
	sp.enableAutoReconnect = false;
  sp.disconnectHandler = disconnectCallbackHandler;

	//打印当前设备iot 连接状态
	debug_print("mqttClient.clientStatus.clientState = %d \n",mqttClient.clientStatus.clientState);
	debug_print("Shadow Init \n");
	rc = aws_iot_shadow_init(&mqttClient, &sp);
	if(SUCCESS != rc) {
		printf("Shadow Init Error \n");
		return rc;
	}
  debug_print("mqttClient.clientStatus.clientState = %d \n",mqttClient.clientStatus.clientState);
	ShadowConnectParameters_t scp = ShadowConnectParametersDefault;
	// scp.pMyThingName  = AWS_IOT_MY_THING_NAME;
	// scp.pMqttClientId = AWS_IOT_MQTT_CLIENT_ID;
	// scp.mqttClientIdLen = (uint16_t) strlen(AWS_IOT_MQTT_CLIENT_ID);
  scp.pMyThingName  = shadow_name;
	scp.pMqttClientId = shadow_id;
	scp.mqttClientIdLen = (uint16_t)strlen(pdev.clientid);

	debug_print("scp.pMyThingName = %s \n",scp.pMyThingName);
	debug_print("scp.pMqttClientId = %s \n",scp.pMqttClientId);
	debug_print("Shadow Start Connect ......\n");
  sprintf(logbuf,"pMyThingName = %s",scp.pMyThingName);
  write_plate_write_IOT_log(logbuf);
	rc = aws_iot_shadow_connect(&mqttClient, &scp);
	if(SUCCESS != rc) {
		printf("Shadow Connection Error \n");
		return rc;
	}
  debug_print("Shadow Connect ok \n");
  sprintf(logbuf,"%s","Shadow Connect ok");
  write_plate_write_IOT_log(logbuf);
	/*
	 * Enable Auto Reconnect functionality. Minimum and Maximum time of Exponential backoff are set in aws_iot_config.h
	 *  #AWS_IOT_MQTT_MIN_RECONNECT_WAIT_INTERVAL
	 *  #AWS_IOT_MQTT_MAX_RECONNECT_WAIT_INTERVAL
	 */
	rc = aws_iot_shadow_set_autoreconnect_status(&mqttClient, true);
	if(SUCCESS != rc) {
		printf("Unable to set Auto Reconnect to true - %d \n", rc);
    sprintf(logbuf,"Unable to set Auto Reconnect to true - %d",rc);
    write_plate_write_IOT_log(logbuf);
		return rc;
	}
  /***********************************shadow delta start*************************************************************/
	rc = aws_iot_shadow_register_delta(&mqttClient, &menuUpdateTimeHandler);
	if(SUCCESS != rc) {
    sprintf(logbuf,"Shadow menuUpdateTimeHandler Register Delta Error =  %d",rc);
    write_plate_write_IOT_log(logbuf);
		printf("Shadow menuUpdateTimeHandler Register Delta Error =  %d\n",rc);
    return rc;
	}

	rc = aws_iot_shadow_register_delta(&mqttClient, &snHandler);
	if(SUCCESS != rc) {
		printf("Shadow snHandler Register Delta Error \n");
    return rc;
	}

  rc = aws_iot_shadow_register_delta(&mqttClient, &restaurantIDHandler);
	if(SUCCESS != rc) {
		printf("Shadow restaurantIDHandler Register Delta Error \n");
    return rc;
	}

  rc = aws_iot_shadow_register_delta(&mqttClient, &versionHandler);
	if(SUCCESS != rc) {
		printf("Shadow versionHandler Register Delta Error \n");
    return rc;
	}
  /***********************************************shadow delta end***********************************************/
  /***********************************************jobs delta start***********************************************/
  //订阅 jobs 固件更新使用
  rc = aws_iot_jobs_subscribe_to_job_messages(
		&mqttClient, QOS0, pdev.name, NULL, JOB_GET_PENDING_TOPIC, JOB_WILDCARD_REPLY_TYPE,
		iot_get_pending_callback_handler, NULL, topicToSubscribeGetPending, sizeof(topicToSubscribeGetPending));
	if(SUCCESS != rc) {
		printf("Error subscribing JOB_GET_PENDING_TOPIC: %d ", rc);
		return rc;
	}

	rc = aws_iot_jobs_subscribe_to_job_messages(
		&mqttClient, QOS0, pdev.name, NULL, JOB_NOTIFY_NEXT_TOPIC, JOB_REQUEST_TYPE,
		iot_next_job_callback_handler, NULL, topicToSubscribeNotifyNext, sizeof(topicToSubscribeNotifyNext));
	if(SUCCESS != rc) {
		printf("Error subscribing JOB_NOTIFY_NEXT_TOPIC: %d ", rc);
		return rc;
	}

	rc = aws_iot_jobs_subscribe_to_job_messages(//get
		&mqttClient, QOS0, pdev.name, JOB_ID_NEXT, JOB_DESCRIBE_TOPIC, JOB_WILDCARD_REPLY_TYPE,
		iot_next_job_callback_handler, NULL, topicToSubscribeGetNext, sizeof(topicToSubscribeGetNext));
	if(SUCCESS != rc) {
		printf("Error subscribing JOB_DESCRIBE_TOPIC ($next): %d ", rc);
		return rc;
	}

	rc = aws_iot_jobs_subscribe_to_job_messages(
		&mqttClient, QOS0, pdev.name, JOB_ID_WILDCARD, JOB_UPDATE_TOPIC, JOB_ACCEPTED_REPLY_TYPE,
		iot_update_accepted_callback_handler, NULL, topicToSubscribeUpdateAccepted, sizeof(topicToSubscribeUpdateAccepted));
	if(SUCCESS != rc) {
		printf("Error subscribing JOB_UPDATE_TOPIC/accepted: %d ", rc);
		return rc;
	}

  rc = aws_iot_jobs_subscribe_to_job_messages(
		&mqttClient, QOS0, pdev.name, JOB_ID_WILDCARD, JOB_UPDATE_TOPIC, JOB_REJECTED_REPLY_TYPE,
		iot_update_rejected_callback_handler, NULL, topicToSubscribeUpdateRejected, sizeof(topicToSubscribeUpdateRejected));
	if(SUCCESS != rc) {
		printf("Error subscribing JOB_UPDATE_TOPIC/rejected: %d ", rc);
		return rc;
	}
  
  paramsQOS0.qos = QOS0;
	paramsQOS0.payload = (void *)cPayload;
	paramsQOS0.isRetained = 0;
	paramsQOS0.payloadLen = strlen(cPayload);
	rc = aws_iot_jobs_send_query(&mqttClient, QOS0, pdev.name, NULL, NULL, topicToPublishGetPending, sizeof(topicToPublishGetPending), NULL, 0, JOB_GET_PENDING_TOPIC);

  AwsIotDescribeJobExecutionRequest describeRequest;
	describeRequest.executionNumber = 0;
	describeRequest.includeJobDocument = true;
	describeRequest.clientToken = NULL;
	rc = aws_iot_jobs_describe(&mqttClient, QOS0, pdev.name, JOB_ID_NEXT, &describeRequest, topicToPublishGetNext, sizeof(topicToPublishGetNext), NULL, 0);
/*******************************************jobs delta end**********************************************************************************************/
  debug_print("Shadow delta ok \n");
  iot_connect_status_bak = mqttClient.clientStatus.clientState;
  sprintf(logbuf,"%s","Shadow delta ok");
  write_plate_write_IOT_log(logbuf);
  //return -1;
  //IOT 后台获取当前 shadow状态
  getShadowFlag = true;//使能定时获取shadow状态任务
  //rc = aws_iot_shadow_get(&mqttClient, pdev.name, GetShadowStatusCallback,NULL, 10, true);
	debug_print("mqttClient.clientStatus.clientState = %d \n",mqttClient.clientStatus.clientState);
  return rc;
}

/*=======================================================================================
* 函 数 名： write_plate_aws_iot_shadow_report_menuUpdateTime
* 参    数： 
* 功能描述:  写盘器AWS IOT SHADOW 上报menuUpdateTime
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
static int aws_iot_shadow_report_menuUpdateTime(void) 
{
  IoT_Error_t rc = FAILURE;

  rc = aws_iot_shadow_init_json_document(JsonDocumentBuffer, sizeOfJsonDocumentBuffer);
  if(SUCCESS == rc) {
    rc = aws_iot_shadow_add_reported(JsonDocumentBuffer, sizeOfJsonDocumentBuffer, 1, &menuUpdateTimeHandler);
    if(SUCCESS == rc) {
      rc = aws_iot_finalize_json_document(JsonDocumentBuffer, sizeOfJsonDocumentBuffer);
      if(SUCCESS == rc) {
        printf("Update menuUpdateTime Shadow: %s \n", JsonDocumentBuffer);
        rc = aws_iot_shadow_update(&mqttClient, pdev.name, JsonDocumentBuffer,
                                    ShadowMenuUpdateTimeUpdateStatusCallback, NULL, TIME_OUT_COUNT, true);
      }
    }
  }
}

/*=======================================================================================
* 函 数 名： aws_iot_shadow_report_restaurantID
* 参    数： 
* 功能描述:  写盘器AWS IOT SHADOW restaurantID（餐厅ID）
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
static int aws_iot_shadow_report_restaurantID(void) 
{
  IoT_Error_t rc = FAILURE;

  rc = aws_iot_shadow_init_json_document(JsonDocumentBuffer, sizeOfJsonDocumentBuffer);
  if(SUCCESS == rc) {
    rc = aws_iot_shadow_add_reported(JsonDocumentBuffer, sizeOfJsonDocumentBuffer, 1, &restaurantIDHandler);
    if(SUCCESS == rc) {
      rc = aws_iot_finalize_json_document(JsonDocumentBuffer, sizeOfJsonDocumentBuffer);
      if(SUCCESS == rc) {
        printf("Update restaurantID Shadow: %s \n", JsonDocumentBuffer);
        rc = aws_iot_shadow_update(&mqttClient, pdev.name, JsonDocumentBuffer,
                        ShadowRestaurantIDUpdateStatusCallback, NULL, TIME_OUT_COUNT, true);
      }
    }
  }
}

/*=======================================================================================
* 函 数 名： aws_iot_shadow_report_romversion
* 参    数： 
* 功能描述:  写盘器AWS IOT SHADOW romversion（当前固件版本）
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
static int aws_iot_shadow_report_romversion(void) 
{
  IoT_Error_t rc = FAILURE;

  memcpy(version,devMsg.version,strlen(devMsg.version));

  rc = aws_iot_shadow_init_json_document(JsonDocumentBuffer, sizeOfJsonDocumentBuffer);
  if(SUCCESS == rc) {
    rc = aws_iot_shadow_add_reported(JsonDocumentBuffer, sizeOfJsonDocumentBuffer, 1, &versionHandler);
    if(SUCCESS == rc) {
      rc = aws_iot_finalize_json_document(JsonDocumentBuffer, sizeOfJsonDocumentBuffer);
      if(SUCCESS == rc) {
        printf("Update romversion Shadow: %s \n", JsonDocumentBuffer);
        rc = aws_iot_shadow_update(&mqttClient, pdev.name, JsonDocumentBuffer,
                           ShadowMenuUpdateRomVersionStatusCallback, NULL, TIME_OUT_COUNT, true);
      }
    }
  }
}

/*=======================================================================================
* 函 数 名： write_plate_aws_iot_shadow_report_sn
* 参    数： 
* 功能描述:  写盘器AWS IOT SHADOW 上报sn
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
static int aws_iot_shadow_report_sn(void) 
{
  IoT_Error_t rc = FAILURE;

  //通过 shadow reported 确认更新
  //组JSON
  cJSON *data_json = cJSON_CreateObject();
  debug_print("devMsg.sn = %s \n",devSn);
  cJSON_AddItemToObject(data_json, "sn", cJSON_CreateString(devSn));
  cJSON_AddItemToObject(data_json, "code", cJSON_CreateString(code));
  //打印JSON
  char *out = cJSON_Print(data_json);
  memset(snDeltaData,0,SHADOW_MAX_SIZE_OF_RX_BUFFER);
  memcpy(snDeltaData,out,strlen(out));
  debug_print("Sending delta message back %s\n", snDeltaData);
  memset(JsonDocumentBuffer,0,MAX_LENGTH_OF_UPDATE_JSON_BUFFER);

  rc = aws_iot_shadow_init_json_document(JsonDocumentBuffer, sizeOfJsonDocumentBuffer);
  if(SUCCESS == rc) {
    rc = aws_iot_shadow_add_reported(JsonDocumentBuffer, sizeOfJsonDocumentBuffer, 1, &snHandler);
    if(SUCCESS == rc) {
      rc = aws_iot_finalize_json_document(JsonDocumentBuffer, sizeOfJsonDocumentBuffer);
      if(SUCCESS == rc) {
        debug_print("Update Shadow Sn: %s \n", JsonDocumentBuffer);
        rc = aws_iot_shadow_update(&mqttClient, pdev.name, JsonDocumentBuffer,
                                    ShadowSnUpdateStatusCallback, NULL, TIME_OUT_COUNT, true);
      }
    }
  }
  free(out);
  cJSON_Delete(data_json);  
}

/*=======================================================================================
* 函 数 名： write_plate_aws_iot_shadow_report_restaurantID
* 参    数： 
* 功能描述:  写盘器AWS IOT SHADOW restaurantID外部调用
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
int write_plate_aws_iot_shadow_report_restaurantID(int64_t id) 
{
  restaurantID = id;
  debug_print("write_plate_aws_iot_shadow_report_restaurantID = %lld \n",restaurantID);
  reportRestaurantIDFlag = true;//上报标记置位，外部线程一直上报状态，直到收到iot回复后标记清除
}

/*=======================================================================================
* 函 数 名： write_plate_aws_iot_shadow_task
* 参    数： 
* 功能描述:  写盘器AWS IOT SHADOW 轮询任务 cAppTask线程任务里面调用
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
int64_t iot_disconnect_time_bak = 0;
int write_plate_aws_iot_shadow_task(void) 
{
  IoT_Error_t rc = FAILURE;
  struct timeval tv;
  struct timezone tz;
  char logbuf[200];
  char shadow_name[200];
  char shadow_id[200];

  debug_print("write_plate_aws_iot_shadow_task = start \n");
  ShadowConnectParameters_t scp = ShadowConnectParametersDefault;
  //此函数可以在单独的线程中使用，等待传入消息，确保使用AWS服务保持连接。它还确保清除Shadow操作的过期请求并执行Timeout回调。
  rc = aws_iot_shadow_yield(&mqttClient, 200);

  if(reportSnFlag == true) {// report sn 码
    reportSnFlag = false;
    aws_iot_shadow_report_sn();
  }  
  if(reportRestaurantIDFlag == true) {//report RestaurantID(餐厅ID)
    reportRestaurantIDFlag = false;
    aws_iot_shadow_report_restaurantID();
  }
  if(reportmenuUpdateTimeFlag == true) {//report menuUpdateTime(菜单版本)
    reportmenuUpdateTimeFlag = false;
    aws_iot_shadow_report_menuUpdateTime();
  } 
  if(reportromVersionFlag == true) {//上报当前固件版本
    reportromVersionFlag = false;
    aws_iot_shadow_report_romversion();
  }
  if(getShadowFlag == true) {//get shadow 状态超时时间 4S
    //getShadowFlag = false;
    debug_print("aws_iot_shadow_get = start \n");
    //sleep(TIME_OUT_COUNT);
    aws_iot_shadow_get(&mqttClient, pdev.name, GetShadowStatusCallback, NULL, TIME_OUT_COUNT, false); 
  }
  if(OTA_UPDATE_STATUS == true) {//上报固件更新结果
    aws_report_iot_update_result(REPORT_OTA_STATUS);
  }
  debug_print("mqttClient.clientStatus.clientState = %d \n",mqttClient.clientStatus.clientState);
  sprintf(logbuf,"mqttClient.clientStatus.clientState = %d",mqttClient.clientStatus.clientState);
  write_plate_write_IOT_log(logbuf);

  if(mqttClient.clientStatus.clientState >= CLIENT_STATE_DISCONNECTING) {//IOT 断开
    if(iot_connect_status_bak == CLIENT_STATE_CONNECTED_IDLE) {
      gettimeofday (&tv , &tz);
      printf("tv_sec_start = %d\n", tv.tv_sec);
      sprintf(logbuf,"tv_sec_start = %d",tv.tv_sec);
      write_plate_write_IOT_log(logbuf);
      iot_disconnect_time_bak = tv.tv_sec;
      iot_connect_status_bak = CLIENT_STATE_DISCONNECTING;
    }  
    gettimeofday (&tv , &tz);
    if((tv.tv_sec - iot_disconnect_time_bak) > 120 ) {//断开连接，超过 60S 后还没重连好，重启一下进程
      printf("time_out_tv_sec = %d\n", tv.tv_sec);
      sprintf(logbuf,"time_out_tv_sec = %d",tv.tv_sec);
      write_plate_write_IOT_log(logbuf);
      getShadowFlag = true;
      sprintf(logbuf,"%s","IOT 重连超时 golang 重启");
      write_plate_write_IOT_log(logbuf);
      system("/home/meican/rebootgolang.sh");
    }
  }
  sleep(1);
}

/*=======================================================================================
* 函 数 名： write_plate_aws_iot_poll_jobs_next
* 参    数： 
* 功能描述:  next/get。设备定期轮询以获取下一个任务（固件更新）。
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-11 
==========================================================================================*/
int write_plate_aws_iot_poll_jobs_next(void) 
{
  char topicToPublishGetPending[MAX_JOB_TOPIC_LENGTH_BYTES];
  char cPayload[100];
  
  IoT_Publish_Message_Params paramsQOS0;

  paramsQOS0.qos = QOS0;
	paramsQOS0.payload = (void *)cPayload;
	paramsQOS0.isRetained = 0;
	paramsQOS0.payloadLen = strlen(cPayload);
	aws_iot_jobs_send_query(&mqttClient, QOS0, pdev.name, NULL, NULL, topicToPublishGetPending, sizeof(topicToPublishGetPending), NULL, 0, JOB_NOTIFY_NEXT_TOPIC);
}

/*=======================================================================================
* 函 数 名： aws_iot_test
* 参    数： 
* 功能描述:  
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-06-22 
==========================================================================================*/
int aws_iot_test() 
{
  IoT_Error_t rc = FAILURE;

	// loop and publish a change in temperature
	while(NETWORK_ATTEMPTING_RECONNECT == rc || NETWORK_RECONNECTED == rc || SUCCESS == rc) 
	{
		rc = aws_iot_shadow_yield(&mqttClient, 200);
		if(NETWORK_ATTEMPTING_RECONNECT == rc) {
			sleep(1);
			// If the client is attempting to reconnect we will skip the rest of the loop.
			continue;
		}
		rc = aws_iot_shadow_init_json_document(JsonDocumentBuffer, sizeOfJsonDocumentBuffer);
		if(SUCCESS == rc) {
			rc = aws_iot_shadow_add_reported(JsonDocumentBuffer, sizeOfJsonDocumentBuffer, 2, &restaurantIDHandler,
											 &menuUpdateTimeHandler);
			if(SUCCESS == rc) {
				rc = aws_iot_finalize_json_document(JsonDocumentBuffer, sizeOfJsonDocumentBuffer);
				if(SUCCESS == rc) {
					printf("Update Shadow: %s \n", JsonDocumentBuffer);
					rc = aws_iot_shadow_update(&mqttClient, AWS_IOT_MY_THING_NAME, JsonDocumentBuffer,
											   ShadowRestaurantIDUpdateStatusCallback, NULL, 4, true);
				}
			}
		}
		printf("*****************************************************************************************\n");
		sleep(1);
	}

	// if(SUCCESS != rc) {
	// 	printf("An error occurred in the loop %d \n", rc);
	// }

	// IOT_INFO("Disconnecting \n");
	// rc = aws_iot_shadow_disconnect(&mqttClient);

	// if(SUCCESS != rc) {
	// 	printf("Disconnect error %d \n", rc);
	// }

	return rc;
}
