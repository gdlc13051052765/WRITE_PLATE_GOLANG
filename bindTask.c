#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <malloc.h>
#include <fcntl.h>
#include <sys/msg.h>
#include <sys/ipc.h>
#include <sys/time.h>
#include <time.h>

#include "bindTask.h"
#include "debug_print.h"


typedef struct item_t {
  char *key;
  char *value;
}ITEM;

/*
 *去除字符串右端空格
 */
static char *strtrimr(char *pstr)
{
  int i;
  i = strlen(pstr) - 1;
  while (isspace(pstr[i]) && (i >= 0))
    pstr[i--] = '\0';
  return pstr;
}
/*
 *去除字符串左端空格
 */
static char *strtriml(char *pstr)
{
  int i = 0,j;
  j = strlen(pstr) - 1;
  while (isspace(pstr[i]) && (i <= j))
    i++;
  if (0<i)
    strcpy(pstr, &pstr[i]);
  return pstr;
}
/*
 *去除字符串两端空格
 */
static char *strtrim(char *pstr)
{
  char *p;
  p = strtrimr(pstr);
  return strtriml(p);
}

/*
 *从配置文件的一行读出key或value,返回item指针
 *line--从配置文件读出的一行
 */
static int get_item_from_line(char *line, struct item_t *item)
{
  char *p = (char *)malloc(sizeof(char)*1000);
  char *p2 = (char *)malloc(sizeof(char)*1000);
 // p = line;
  p = strtrim(line);//删除空格的函数
  int len = sizeof(line);
 // debug_print("len =%d\n",len);
  if(len <= 0){
    debug_print("空行 \n");
    return 1;//空行
  }
  else if(p[0]=='#'){
    return 2;
  }else{
    p2 = strchr(p, '=');
    *p2++ = '\0';
    item->key = (char *)malloc(strlen(p) + 1);
    item->value = (char *)malloc(strlen(p2) + 1);
    strcpy(item->key,p);
    strcpy(item->value,p2);
  }
  return 0;//查询成功
}

static int file_to_items(const char *file, struct item_t *items, int *num)
{
  char line[1024];
  FILE *fp;
  fp = fopen(file,"r");
  if(fp == NULL)
    return 1;
  int i = 0;
  while(fgets(line, 1023, fp))
  {
    char *p = strtrim(line);
    int len = strlen(p);
    if(len <= 0)
    {
      continue;
    }
    else if(p[0]=='#')
    {
      continue;
    }
    else if(p[0]=='}')
    {
      continue;
    }
    else
    {
      char *p2 = strchr(p, '=');
      /*这里认为只有key没什么意义*/
      if(p2 == NULL)
        continue;
      *p2++ = '\0';
      items[i].key = (char *)malloc(strlen(p) + 1);
      items[i].value = (char *)malloc(strlen(p2) + 1);
      strcpy(items[i].key,p);
      strcpy(items[i].value,p2);

      i++;
    }
  }
  (*num) = i;
  fclose(fp);
  return 0;
}

/*
 *读取value
 */
static int read_conf_value(const char *key, char *value1, const char *file)
{
  char line[1000]="0";
  FILE *fp;
  fp = fopen(file,"r");
  if(fp == NULL)
  {
    debug_print("open file error\n");
      return 1;//文件打开错误
  }

  while (fgets(line, 2047, fp)!=NULL)
  {
    ITEM item;
 //   debug_print("line len = %d\n",strlen(line));
    if(strlen(line) <2)
      line[strlen(line)-1] ='\0';
    else
    {
      if(!get_item_from_line(line,&item))//查询成功
      {
        // debug_print("item.key = %s\n",item.key);
        // debug_print("item.value = %s\n",item.value);
        if(!strcmp(item.key,key)) {
          strcpy(value1,item.value);
          free(item.key);
          free(item.value);
          break;
        }
      }
    } 
  }
  fclose(fp);
  return 0;//成功
}

static int write_conf_value(const char *key, char *value, const char *file)
{
  ITEM items[20];// 假定配置项最多有20个
  int num;//存储从文件读取的有效数目
  file_to_items(file, items, &num);

  int i=0;
  //查找要修改的项
  for(i=0;i<num;i++) {
    if(!strcmp(items[i].key, key)){
      items[i].value = value;
      break;
    }
  }

  // 更新配置文件,应该有备份，下面的操作会将文件内容清除
  FILE *fp;
  fp = fopen(file, "w");
  if(fp == NULL)
    return 1;

  i=0;
  for(i=0;i<num;i++) {
    fprintf(fp,"%s=%s\n",items[i].key, items[i].value);
  }
  fprintf(fp,"%s\n","}");//最后一行写入一个括号
  fclose(fp);
  //清除工作
/* i=0;
  for(i=0;i<num;i++){
      free(items[i].key);
      free(items[i].value);
  }*/
  return 0;
}

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

/*=======================================================================================
* 函 数 名： write_wifi_ssid_passed_txt
* 参    数： 
* 功能描述:  将获取wifi 账号密码写道配置文件里面
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-05-11 
==========================================================================================*/
static int write_wifi_ssid_passed_txt(char *ssid,char *psk)
{
  char *key;
  char *value=NULL;
  char *file;
  FILE *fp;
  ITEM items[20];// 假定配置项最多有20个
  int num;//存储从文件读取的有效数目

  file="/etc/wpa_supplicant.conf";

  value=(char *)malloc(sizeof(char)*500); 
  //wifi  ssid
  key="ssid";
  write_conf_value(key,ssid,file);
  read_conf_value(key,value,file);
  printf("ssid = %s\n",value);

  //wifi passed
  key="psk";
  write_conf_value(key,psk,file);
  read_conf_value(key,value,file);
  printf("psk = %s\n",value);

  key = NULL;
  value = NULL;
}

/*=======================================================================================
* 函 数 名： get_wifi_ssid_passed
* 参    数： 
* 功能描述:  获取wifi 账号密码
* 返 回 值： 
* 备    注： 
* 作    者： lc
* 创建时间： 2021-05-11 
==========================================================================================*/
int get_wifi_ssid_passed(void)
{
  int ret = 0;
  char ssid[33],ssid1[33]; /* ssid of 32-char length, plus trailing '\0' */
  char password[65],password1[65]; /* password is 64-char length, plus trailing '\0' */

  system("./setwifi.sh");
  sleep(5);
  ret = wifi_config_setup_start();
  if (ret) return ret;

  ret = easy_setup_query();
  if (!ret) {   
    wifi_config_setup_get_ssid_password(ssid, password);
    sprintf(ssid1,"\"%s\"",ssid);
    sprintf(password1,"\"%s\"",password);
    write_wifi_ssid_passed_txt(ssid1, password1);
  }
  system("ifconfig wlan0 down");
  sleep(3);
  system("/home/mc_shell/wifi_connect.sh");
  sleep(5);
  // sprintf(ssid,"\"RobotPort\"");
  // sprintf(password,"\"ilovedota\"");
  // write_wifi_ssid_passed_txt(ssid, password);
}
