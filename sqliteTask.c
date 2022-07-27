/*****************************************************************************************
 * 文件说明：
 * SQLITE3 数据库管理写盘器配置数据库，菜单数据库的创建，查询，插入，修改等
 * 
 *****************************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>

#include "sqlite3.h"
#include "sqliteTask.h"
#include "debug_print.h"
#include "msgTask.h"

static char *zErrMsg = NULL;
static char har_ver[] = "wr_01";
static char soft_ver[] = "v0.0.0";
static char soft_verbak[] = "v0.0.0";
static char shadow_name[] = "Thing_cardWriterV2_12467b16";
static char shadow_id[] = "12467b16";
static char main_m_name[] = "menu_lev1";
static char menu_type[] = "01";
static sqlite_int64  menu_ver = 1555572154506;
static sqlite_int64  new_menu_ver = 1555572154506;
static char address[] = "北京市朝阳区酒仙桥路美餐公司大食堂";
static int dev_status = 0;
static int menu_level = 4;
static int Indent_code = 215;
static char uuid[] = "";
static char sn[] = "";
static char JodID[] = "";
static char OtaResult[] = "ok";
static int v2id = 0;
static sqlite_int64  restaurantid = 155;//餐厅ID

static char qt_run[] = "";
static char golang_run[] = "";

//QT选择要写盘的数据到本数据库，写盘时从本数据库读取数据
//sqlite3 *writePlateMenu_db =NULL;

// Note: Typical values of SCNd64 include "lld" and "ld".
//字符串转int64
static int64_t S64(const char *s) {
  int64_t i;
  char c ;
  int scanned = sscanf(s, "%" SCNd64 "%c", &i, &c);
  if (scanned == 1) return i;
  if (scanned > 1) {
    // TBD about extra data found
    return i;
  }
  // TBD failed to scan;  
  return 0;  
}

/*==================================================================================
* 函 数 名： sqlite_create_process_protection_db
* 参    数： 
* 功能描述:  创建进程保护数据库
* 返 回 值： None
* 备    注： 创建成功返回0
* 作    者： lc
* 创建时间： 2021-09-27
==================================================================================*/
int sqlite_create_process_protection_db(void)
{
  int err;
  char tempdata[500];
  sqlite3 *process_protection_db =NULL;

  /* 创建进程保护数据库 */
  err = sqlite3_open("/home/meican/process_protection.db",&process_protection_db);
  if( err ) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(process_protection_db));
    sqlite3_close(process_protection_db);
    return err;
  }
  else 
    debug_print("You have opened a sqlite3 database named process_protection_db successfully!\n");
  //qt运行标志位 qt_run golang运行标志位 golang_run 
  char *sql = "create table process_protection_db (qt_run char, golang_run char);";
  sqlite3_exec(process_protection_db,sql,NULL,NULL,&zErrMsg);
  sqlite3_close(process_protection_db);

  //插入数据
  err = sqlite3_open("/home/meican/process_protection.db",&process_protection_db);
  if( err ) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(process_protection_db));
    sqlite3_close(process_protection_db);
    return err;
  }
  sprintf(tempdata,"insert into process_protection_db values('%s','%s');", qt_run, golang_run);

  debug_print("process_protection_db insertdata = %s\n", tempdata);
  err = sqlite3_exec(process_protection_db,tempdata,NULL,NULL,&zErrMsg);
  sqlite3_close(process_protection_db);
  return err;
}

/*==================================================================================
* 函 数 名： sqlite_update_process_protection_db
* 参    数： 
* 功能描述:  修改进程数据库运行标志位
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-09-27 //
==================================================================================*/
int sqlite_update_process_protection_db(void)
{
  int err;
  char tempdata[300];
  sqlite3 *process_protection_db =NULL;

  err = sqlite3_open_v2("/home/meican/process_protection.db", &process_protection_db, SQLITE_OPEN_READWRITE, NULL);
  if(err) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(process_protection_db));
    sqlite3_close_v2(process_protection_db);
    return err;
  }
  sprintf(tempdata,"update process_protection_db set golang_run ='ok' ");//
  debug_print("tempdata = %s \n", tempdata);
  err = sqlite3_exec(process_protection_db, tempdata, NULL, NULL, &zErrMsg);
  sqlite3_close_v2(process_protection_db);
  return err;
}

/*==================================================================================
* 函 数 名： sqlite_update_process_protection_db_null
* 参    数： 
* 功能描述:  清除进程数据库运行标志位
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-09-27 //
==================================================================================*/
int sqlite_update_process_protection_db_null(void)
{
  int err;
  char tempdata[300];
  sqlite3 *process_protection_db =NULL;

  err = sqlite3_open_v2("/home/meican/process_protection.db", &process_protection_db, SQLITE_OPEN_READWRITE, NULL);
  if(err) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(process_protection_db));
    sqlite3_close_v2(process_protection_db);
    return err;
  }
  sprintf(tempdata,"update process_protection_db set golang_run ='', qt_run = '' ");//
  debug_print("tempdata = %s \n", tempdata);
  err = sqlite3_exec(process_protection_db, tempdata, NULL, NULL, &zErrMsg);
  sqlite3_close_v2(process_protection_db);
  return err;
}

/*==================================================================================
* 函 数 名： sqlite_create_config_db
* 参    数： 
* 功能描述:  创建设备参数配置数据库
* 返 回 值： None
* 备    注： 创建成功返回0
* 作    者： lc
* 创建时间： 2021-05-25
==================================================================================*/
int sqlite_create_config_db(void)
{
  int err;
  char tempdata[500];
  sqlite3 *config_db =NULL;

  /* 创建基础信息数据库 */
  err = sqlite3_open("/home/meican/base_config.db",&config_db);
  if( err ) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close(config_db);
    return err;
  }
  else 
    debug_print("You have opened a sqlite3 database named config_db successfully!\n");
  //硬件版本 har_ver 软件版本 soft_ver 字符编号 cha_encod 字库名称 font _name 主菜单表明 main_m_name 菜单类型版本 menu_type
  //菜单版本 menu_ver 食堂地址 address 设备状态 dev_status 菜单等级总数 menu_level 美餐识别码 Indent_code
  char *sql = "create table config (har_ver char, soft_ver char,shadow_name char,shadow_id char ,main_m_name char,menu_type char,menu_ver INTEGER, new_menu_ver INTEGER, address char, dev_status INTEGER,menu_level INTEGER, indent_code INTEGER,uuid char,sn char,v2id INTEGER,restaurantID INTEGER,softWare_bak char,jobId char,otaResult char);";
  sqlite3_exec(config_db,sql,NULL,NULL,&zErrMsg);
  sqlite3_close(config_db);

  //插入数据
  err = sqlite3_open("/home/meican/base_config.db",&config_db);
  if( err ) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close(config_db);
    return err;
  }
  sprintf(tempdata,"insert into config values('%s','%s','%s','%s','%s','%s',%lld,%lld,'%s',%d,%d,%d,'%s','%s',%d,%lld,'%s','%s','%s');",
          har_ver,soft_ver,shadow_name,shadow_id,main_m_name,menu_type,menu_ver,new_menu_ver,address,dev_status,menu_level,Indent_code,uuid,sn,v2id,restaurantid,soft_verbak,JodID,OtaResult);

  debug_print("config insertdata = %s\n", tempdata);
  err = sqlite3_exec(config_db,tempdata,NULL,NULL,&zErrMsg);
  sqlite3_close(config_db);
  return err;
}

/*==================================================================================
* 函 数 名： sqlite_create_food_menu_db
* 参    数： None
* 功能描述:  创建写盘菜单数据库
* 返 回 值： None
* 备    注： 创建成功返回0
* 作    者： lc
* 创建时间： 2021-04-22 
==================================================================================*/
int sqlite_create_food_menu_db(void)
{
  int err;
  char tempdata[200];
  sqlite3 *writePlateMenu_db =NULL;
 
  /* 创建写盘信息数据库 */
  err = sqlite3_open("/home/meican/writeplatemenu.db",&writePlateMenu_db);
  if( err )
  {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(writePlateMenu_db));
    sqlite3_close(writePlateMenu_db);
    return err;
  }
  else 
    debug_print("You have opened a writeplatemenu database named writePlateMenu_db successfully!\n");
  //菜单ID，菜单名称context，餐品ID dish_id，菜品价格price,status=0,菜单未启用，status =1;菜单已启用
  char *sql = "create table writeplatemenu (id int,context char,dish_id int,price int,status int);";
  sqlite3_exec(writePlateMenu_db,sql,NULL,NULL,&zErrMsg);
    //插入数据
  debug_print("writePlateMenu_db insert ok \n");
  sprintf(tempdata,"insert into writeplatemenu values(%d,'%s',%d,%d,%d);",0,NULL,NULL,NULL,0);
  debug_print("writeplatemenu insertdata = %s\n", tempdata);
  err = sqlite3_exec(writePlateMenu_db,tempdata,NULL,NULL,&zErrMsg);
  sqlite3_close(writePlateMenu_db);
}

/*==================================================================================
* 函 数 名： sqlite_read_devMsg_from_config_db
* 参    数： 
* 功能描述:  从配置数据库读取设备信息
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-05-25 
==================================================================================*/
static  char gloalUuid[100];
static  char gloalSn[100];
static  char gloalHardVersion[100];
static  char gloalVersion[100];
static  char gloalVersionBak[100];

C_DevMsgSt sqlite_read_devMsg_from_config_db()
{
  int err =-1,dev_status = -1,i,hardNum;
  int nrow,ncolumn;
  char * errmsg = NULL;
  char **azResult; //是 char ** 类型，两个*号
  sqlite3 *config_db =NULL;
  C_DevMsgSt pdev ;


  /* 创建基础信息数据库 */
  err = sqlite3_open_v2("/home/meican/base_config.db",&config_db,SQLITE_OPEN_READONLY, NULL);
 // err = sqlite3_open("/home/meican/base_config.db",&config_db);
  if( err ) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return pdev;
  }
  //配置数据库读取数据
  char *sql = "select * from config";
  err = sqlite3_get_table(config_db, sql, &azResult, &nrow, &ncolumn, &zErrMsg);
  if( err ) {
    debug_print("Can't select from config: %s\n", sqlite3_errmsg(config_db));
    sqlite3_free_table(azResult);
    sqlite3_free(zErrMsg);
    sqlite3_close_v2(config_db);
    return pdev;
  }
  for(i=0;i<(nrow+1)*ncolumn;i++)
  {
    debug_print("azResult[%d]=%s\n",i,azResult[i]);
  }
  hardNum = 19;
  pdev.status = atoi(azResult[hardNum+9]);//设备状态
  pdev.indent_code = atoi(azResult[hardNum+11]);//每餐识别码
  memset(gloalUuid, 0, 100);
  memset(gloalSn, 0, 100);
  memcpy(gloalUuid, azResult[hardNum+12], strlen(azResult[hardNum+12]));
  memcpy(gloalSn, azResult[hardNum+13], strlen(azResult[hardNum+13]));
  memcpy(gloalHardVersion, azResult[hardNum], strlen(azResult[hardNum]));
  memcpy(gloalVersion, azResult[hardNum+1], strlen(azResult[hardNum+1]));
  memcpy(gloalVersionBak, azResult[hardNum+16], strlen(azResult[hardNum+16]));
  pdev.versionBak = gloalVersionBak;
  pdev.version = gloalVersion;
  pdev.hardVersion = gloalHardVersion;
  pdev.uuid = gloalUuid;//uuid
  pdev.sn = gloalSn;//sn码
  pdev.id = atoi(azResult[hardNum+14]);//设备id
  pdev.restaurantID = atoi(azResult[hardNum+15]);//餐厅id
  
  // debug_print("dev_status = %d\n",pdev.status);
  // debug_print("indent_code = %d\n",pdev.indent_code);
  // debug_print("uuid = %s\n",pdev.uuid);
  // debug_print("sn = %s\n",pdev.sn);
  // debug_print("closetid = %d\n",pdev.id);

  sqlite3_free_table(azResult);
  sqlite3_free(zErrMsg);
  sqlite3_close_v2(config_db);

  return pdev;
}

/*==================================================================================
* 函 数 名： sqlite_read_menuMsg_from_config_db
* 参    数： 
* 功能描述:  从配置数据库读取菜单信息
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-05-25 
==================================================================================*/
C_menuMsgSt sqlite_read_menuMsg_from_config_db(void)
{
  int err =-1,dev_status = -1,i,hardNum;
  int nrow,ncolumn;
  char * errmsg = NULL;
  char **azResult; //是 char ** 类型，两个*号
  sqlite3 *config_db =NULL;
  C_menuMsgSt pdev;

  /* 创建基础信息数据库 */
  err = sqlite3_open_v2("/home/meican/base_config.db",&config_db,SQLITE_OPEN_READONLY, NULL);
 // err = sqlite3_open("/home/meican/base_config.db",&config_db);
  if( err ) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return pdev;
  }
  //配置数据库读取数据
  char *sql = "select * from config";
  err = sqlite3_get_table(config_db, sql, &azResult, &nrow, &ncolumn, &zErrMsg);
  if( err ) {
    debug_print("Can't select from config: %s\n", sqlite3_errmsg(config_db));
    sqlite3_free_table(azResult);
    sqlite3_free(zErrMsg);
    sqlite3_close_v2(config_db);
    return pdev;
  }
  //for(i=0;i<(nrow+1)*ncolumn;i++)
  // {
  //   debug_print("azResult[%d]=%s\n",i,azResult[i]);
  // }
  hardNum = 25;
  pdev.menu_ver = S64(azResult[25]);//菜单版本
  pdev.new_menu_ver = S64(azResult[hardNum+1]);//需要更新的菜单版本
  pdev.menu_level = atoi(azResult[hardNum+4]);//菜单等级
  
 // debug_print("pdev.menu_ver = %lld\n",pdev.menu_ver);
  sqlite3_free_table(azResult);
  sqlite3_free(zErrMsg);
  sqlite3_close_v2(config_db);
  return pdev;
}

/*==================================================================================
* 函 数 名： sqlite_update_menuMsg_to_config_db
* 参    数： 
* 功能描述:  修改配置数据库菜单信息
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-05-25 
==================================================================================*/
int sqlite_update_menuMsg_to_config_db(C_menuMsgSt menuSt)
{
  int err;
  char tempdata[200];
  sqlite3 *config_db =NULL;

  /* 创建基础信息数据库 */
  err = sqlite3_open_v2("/home/meican/base_config.db",&config_db,SQLITE_OPEN_READWRITE, NULL);
  //err = sqlite3_open("/home/meican/base_config.db",&config_db);
  if( err ) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return err;
  }

  sprintf(tempdata,"update config set new_menu_ver=%lld,menu_ver=%lld,menu_level=%d where v2id>=0",menuSt.new_menu_ver ,menuSt.menu_ver,menuSt.menu_level);//
  debug_print("tempdata = %s \n",tempdata);
  err = sqlite3_exec(config_db,tempdata,NULL,NULL,&zErrMsg);
  sqlite3_close_v2(config_db);
  if(!err) {
    write_plate_updata_menu_version(menuSt.menu_ver, menuSt.new_menu_ver);//更改golang 写盘器菜单版本
  }
  return err;
}

/*==================================================================================
* 函 数 名： sqlite_update_devMsg_to_config_db
* 参    数： 修改被指数据库设备信息
* 功能描述:  修改配置数据库参数
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-05-25 //
==================================================================================*/
int sqlite_update_devMsg_to_config_db(C_DevMsgSt pdev)
{
  int err;
  char tempdata[500];
  sqlite3 *config_db =NULL;

  /* 创建基础信息数据库 */
  err = sqlite3_open_v2("/home/meican/base_config.db",&config_db,SQLITE_OPEN_READWRITE, NULL);
 // err = sqlite3_open("/home/meican/base_config.db",&config_db);
  if(err) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return err;
  }
  sprintf(tempdata,"update config set uuid='%s',sn='%s',v2id=%d, dev_status=%d where v2id>=0",pdev.uuid,pdev.sn,pdev.id,pdev.status);//
  debug_print("tempdata = %s \n",tempdata);
  err = sqlite3_exec(config_db,tempdata,NULL,NULL,&zErrMsg);
  sqlite3_close_v2(config_db);
  return err;
}

/*==================================================================================
* 函 数 名： sqlite_create_menu_db
* 参    数： 要创建的数据库名字
* 功能描述:  创建菜单数据库
* 返 回 值： None
* 备    注： 创建成功返回0
* 作    者： lc
* 创建时间： 2021-05-25
==================================================================================*/
int sqlite_create_menu_db(char* dbname)
{
  int err;
  char tempdata[200];
  sqlite3 *Menu_db =NULL;

  /* 创建菜单数据库 */
  sprintf(tempdata,"/home/meican/menudb/%s.db",dbname);//生成数据库名字
  debug_print("create dbname = %s \n",tempdata);
  err = sqlite3_open(tempdata,&Menu_db);
  if( err ) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(Menu_db));
    sqlite3_close(Menu_db);
    return err;
  }
  else 
    debug_print("You have opened sqlite3 database named Menu_db successfully!\n");
  //菜单ID，上级菜单premenu，下级菜单nextmenu，当前等级grade，菜单名称context，菜单拼音spell，餐品ID dish_id
  char *sql = "create table menu (id int,premenu char,nextmenu char,grade int,context char,spell char,dish_id int);";
  err = sqlite3_exec(Menu_db,sql,NULL,NULL,&zErrMsg);
  sqlite3_close(Menu_db);
  return err;
}

/*=================================================================================================================================
* 函 数 名： sqlite_insert_data_to_menu_db
* 参    数： 
* 功能描述:  插入数据到数据库dbname 上级菜单premenu，下级菜单nextmenu，当前等级grade，菜单名称context，菜单拼音spell，餐品ID dish_id，菜品价格price
* 返 回 值： 插入成功返回0
* 备    注： 
* 作    者： lc
* 创建时间： 2021-05-27 
===================================================================================================================================*/
int sqlite_insert_data_to_menu_db(C_MenuDataSt pmenust)
{
  char tempdata[300];
  uint8_t menu_id = 0;//菜单ID
  int err = 0;
  sqlite3_stmt *stmt = NULL; // 用来取数据的
  sqlite3 *Menu_db =NULL;

  sprintf(tempdata,"/home/meican/menudb/%s.db",pmenust.dbname);//生成数据库名字
  err = sqlite3_open(tempdata,&Menu_db);
  if( err ) {
    sqlite3_close(Menu_db);
    return SQLITE_ERROR ;
  }
  //查找最大id
  sprintf(tempdata,"select max(cast(id as int)) from menu");
  if (sqlite3_prepare_v2(Menu_db, tempdata, -1, &stmt, NULL) == SQLITE_OK) {
    while(sqlite3_step(stmt) == SQLITE_ROW ) 
    {	
      // 取出第0列字段的值ID号
      menu_id = sqlite3_column_int(stmt, 0);// 取出第0列字段的值
    }
    sqlite3_finalize(stmt);
    debug_print("menu max id = %d\n", menu_id);
    menu_id++;
  }
  //插入数据
  sprintf(tempdata,"insert into menu values(%d,'%s','%s',%d,'%s','%s',%d);",
          menu_id, pmenust.premenu, pmenust.nextmenu, pmenust.grade, pmenust.context, pmenust.spell, pmenust.dish_id);
  debug_print("menu insertdata= %s\n", tempdata);
  err = sqlite3_exec(Menu_db,tempdata,NULL,NULL,&zErrMsg);
  if(pmenust.dish_id == -1) {//此字段无数据清空
    char *sql = "update menu set dish_id = null where dish_id";
    sqlite3_exec(Menu_db,sql,NULL,NULL,&zErrMsg);
  }
  sqlite3_close(Menu_db);  
  return err;
}

/*================================================================================================================================
* 函 数 名： sqlite_insert_menu_db
* 参    数： 
* 功能描述:  插入数据到数据库 菜单名称context，餐品ID dish_id，菜品价格price
* 返 回 值： 插入成功返回0
* 备    注： 
* 作    者： lc
* 创建时间： 2021-04-22 
===================================================================================================================================*/
int sqlite_write_food_menu_db(char* context, int dish_id, int price)
{
  char tempdata[200];
  char logbuf[200];
  int err,temp = 0;
  sqlite3_stmt *stmt = NULL; // 用来取数据的
  sqlite3 *writePlateMenu_db =NULL;

  err = sqlite3_open_v2("/home/meican/writeplatemenu.db", &writePlateMenu_db, SQLITE_OPEN_READWRITE, NULL);
  if( err ) {
    debug_print("Can't write from writeplatemenu: %s\n", sqlite3_errmsg(writePlateMenu_db));
    sqlite3_close_v2(writePlateMenu_db);
    debug_print("writeplatemenu write err = %d\n",err);
    sprintf(logbuf,"writeplatemenu write err= %d",err);
    write_plate_write_sqlite_log(logbuf);
    return SQLITE_ERROR ;
  }
  sprintf(logbuf,"writeplatemenu write ok = %d, dish_id = %d", err, dish_id);
  write_plate_write_sqlite_log(logbuf);
  //dish_id = 100;
  sprintf(tempdata,"update writeplatemenu set dish_id=%d,status = %d where id>=0", dish_id, 1);//
  debug_print("tempdata = %s \n",tempdata);
  err = sqlite3_exec(writePlateMenu_db, tempdata, NULL, NULL, &zErrMsg);
  if (err != SQLITE_OK) {
    debug_print("writeplatemenu err = %d \n",err);
    sprintf(logbuf,"writeplatemenu sqlite3_exec err = %d", err);
    write_plate_write_sqlite_log(logbuf);
  }

  sqlite3_close_v2(writePlateMenu_db);
  return err;
}

/*==================================================================================
* 函 数 名： sqlite_read_writePlateMsg_from_dishmenu
* 参    数： None
* 功能描述:  从写盘数据数据库读取要写盘的信息
* 返 回 值： None
* 备    注： 返回写盘信息结构体 
* 作    者： lc
* 创建时间： 2021-04-23 
====================================================================================*/
dishMsgSt sqlite_read_writePlateMsg_from_dishmenu(void)
{
  char tempdata[200];
  char logbuf[200];
  int err,i ;
  int nrow,ncolumn;
  char * errmsg = NULL;
  char **azResult; //是 char ** 类型，两个*号
  sqlite3_stmt *stmt = NULL; // 用来取数据的
  dishMsgSt dishMsg;
  sqlite3 *writePlateMenu_db =NULL;

  err = sqlite3_open_v2("/home/meican/writeplatemenu.db",&writePlateMenu_db,SQLITE_OPEN_READONLY, NULL);
  if( err ) {
    debug_print("Can't open from writeplatemenu: %s\n", sqlite3_errmsg(writePlateMenu_db));
    sqlite3_close_v2(writePlateMenu_db);
    debug_print("open writeplatemenu fail = %d\n",err);
    sprintf(logbuf,"open writeplatemenu fail err = %d",err);
    write_plate_write_sqlite_log(logbuf);
    dishMsg.res = err;
    return dishMsg ;
  }
 
  char *sql = "select * from writeplatemenu";
  err = sqlite3_get_table(writePlateMenu_db, sql, &azResult, &nrow, &ncolumn, &zErrMsg);
  if( err ) {
    debug_print("Can't select from conwritePlateMenu_dbfig: %s\n", sqlite3_errmsg(writePlateMenu_db));
    sqlite3_free_table(azResult);
    sqlite3_free(zErrMsg);
    sqlite3_close_v2(writePlateMenu_db);
    dishMsg.res = err;
    return dishMsg ;
  }
  // for(i=0;i<(nrow+1)*ncolumn;i++)
  // //for(i=0;i<2*ncolumn;i++)
  // {
  //   debug_print("azResult[%d]=%s\n",i,azResult[i]);
  // }
  dishMsg.dishid = atoi(azResult[7]);
  sqlite3_close_v2(writePlateMenu_db);
  dishMsg.res = SQLITE_OK;
  sprintf(logbuf,"read writeplatemenu ok err = %d, dishMsg.dishid = %d", err, dishMsg.dishid);
  write_plate_write_sqlite_log(logbuf);
  return dishMsg;
}

/*================================================================================================================================
* 函 数 名： sqlite_read_device_satus
* 参    数： 
* 功能描述:  从配置数据库读取设备状态  0=生产状态，1=出场绑定状态，2=工作状态
* 返 回 值： 成功返回设备状态，失败返回 -1   
* 备    注： 
* 作    者： lc
* 创建时间： 2021-05-27 
===================================================================================================================================*/
int sqlite_read_device_satus(void)
{
  int err =-1,dev_status = -1,i;
  int nrow,ncolumn;
  char * errmsg = NULL;
  char **azResult; //是 char ** 类型，两个*号
  sqlite3 *config_db =NULL;

  /* 创建基础信息数据库 */
  err = sqlite3_open_v2("/home/meican/base_config.db",&config_db,SQLITE_OPEN_READONLY, NULL);
  if( err ) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close(config_db);
    return dev_status;
  }
  //配置数据库查找设备状态
  char *sql = "select dev_status from config";
  err = sqlite3_get_table(config_db, sql, &azResult, &nrow, &ncolumn, &zErrMsg);
  if( err ) {
    debug_print("Can't select dev_status: %s\n", sqlite3_errmsg(config_db));
    sqlite3_free_table(azResult);
    sqlite3_free(zErrMsg);
    sqlite3_close_v2(config_db);
    return dev_status;
  }
  for(i=0;i<(nrow+1)*ncolumn;i++)
  {
    debug_print("azResult[%d]=%s\n",i,azResult[i]);
  }
  dev_status = atoi(azResult[1]);//设备状态赋值
  debug_print("dev_status = %d\n",dev_status);
  sqlite3_free_table(azResult);
  sqlite3_free(zErrMsg);
  sqlite3_close_v2(config_db);
  return dev_status;
}

/*==================================================================================
* 函 数 名： sqlite_update_dev_status_config_db
* 参    数： 
* 功能描述:  修改配置数据库设备状态
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-05-25 //
==================================================================================*/
int sqlite_update_dev_status_config_db(int status)
{
  int err;
  char tempdata[500];
  sqlite3 *config_db =NULL;

  /* 创建基础信息数据库 */
  err = sqlite3_open_v2("/home/meican/base_config.db",&config_db,SQLITE_OPEN_READWRITE, NULL);
  if(err) {
    debug_print("can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return err;
  }
  sprintf(tempdata,"update config set dev_status=%d where v2id>=0",status);//
  debug_print("tempdata = %s \n",tempdata);
  err = sqlite3_exec(config_db,tempdata,NULL,NULL,&zErrMsg);
  sqlite3_close_v2(config_db);
  if(!err)
    write_plate_updata_dev_status(status);
  return err;
}

/*==================================================================================
* 函 数 名： sqlite_update_dev_restaurantId_config_db
* 参    数： 
* 功能描述:  修改配置数据库餐厅ID
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-05-25 //
==================================================================================*/
int sqlite_update_dev_restaurantId_config_db(int64_t id)
{
  int err;
  char tempdata[500];
  sqlite3 *config_db =NULL;

  /* 创建基础信息数据库 */
  err = sqlite3_open_v2("/home/meican/base_config.db",&config_db,SQLITE_OPEN_READWRITE, NULL);
  if(err) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return err;
  }
  sprintf(tempdata, "update config set restaurantID=%lld where v2id>=0", id);//
  debug_print("tempdata = %s \n",tempdata);
  err = sqlite3_exec(config_db, tempdata, NULL, NULL, &zErrMsg);
  sqlite3_close_v2(config_db);
  if(!err)
    write_plate_updata_restaurantID(id);//更改
  return err;
}

/*==================================================================================
* 函 数 名： sqlite_update_dev_sn_config_db
* 参    数： 
* 功能描述:  修改配置数据库sn码
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-05-25 //
==================================================================================*/
int sqlite_update_dev_sn_config_db(char *snbuf, char *code)
{
  int err,codeNum;
  char tempdata[500];
  sqlite3 *config_db =NULL;

  /* 创建基础信息数据库 */
  //err = sqlite3_open("/home/meican/base_config.db",&config_db);
  err = sqlite3_open_v2("/home/meican/base_config.db", &config_db, SQLITE_OPEN_READWRITE, NULL);
  if(err) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return err;
  }
  codeNum = atoi(code);
  sprintf(tempdata, "update config set sn='%s',v2id= %d where v2id>=0", snbuf, codeNum);//
  debug_print("tempdata = %s \n", tempdata);
  err = sqlite3_exec(config_db, tempdata, NULL, NULL, &zErrMsg);
  sqlite3_close_v2(config_db);
  return err;
}

/*==================================================================================
* 函 数 名： sqlite_update_version_config_db
* 参    数： 
* 功能描述:  修改配置数据库软件版本
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-05-25 //
==================================================================================*/
int sqlite_update_version_config_db(char *str)
{
  int err;
  char tempdata[500];
  //char ver[100];
  sqlite3 *config_db =NULL;

  // memset(ver,0,100);
  // //从软件版本txt读取软件版本
  // read_version_from_txt(ver);
  // debug_print("version = %s \n", ver);

  /* 创建基础信息数据库 */
  //err = sqlite3_open("/home/meican/base_config.db",&config_db);
  err = sqlite3_open_v2("/home/meican/base_config.db", &config_db, SQLITE_OPEN_READWRITE, NULL);
  if(err) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return err;
  }
  sprintf(tempdata,"update config set soft_ver='%s' where v2id>=0", str);//
  debug_print("tempdata = %s \n", tempdata);
  err = sqlite3_exec(config_db, tempdata, NULL, NULL, &zErrMsg);
  sqlite3_close_v2(config_db);
  return err;
}

/*==================================================================================
* 函 数 名： sqlite_update_versionBak_config_db
* 参    数： 
* 功能描述:  修改配置数据库软件备份临时版本，固件更新完下次启动时读取跟软件版本字段比较
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-05-25 //
==================================================================================*/
int sqlite_update_versionBak_config_db(char *jobid)
{
  int err;
  char tempdata[500];
  char ver[100], verBak[100];
  sqlite3 *config_db =NULL;
  int nrow, ncolumn;
  char **azResult; //是 char ** 类型，两个*号

  memset(verBak,0,100);
  /* 打开基础信息数据库 */
  err = sqlite3_open_v2("/home/meican/base_config.db",&config_db,SQLITE_OPEN_READONLY, NULL);
  if(err) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return ;
  }
  //查找soft_ver名字
  char *sql = "select soft_ver from config";
  err = sqlite3_get_table(config_db, sql, &azResult, &nrow, &ncolumn, &zErrMsg);
  if(err) {
    debug_print("Can't select soft_ver: %s\n", sqlite3_errmsg(config_db));
    sqlite3_free_table(azResult);
    sqlite3_free(zErrMsg);
    sqlite3_close_v2(config_db);
    return ;
  }
  memcpy(verBak, azResult[1], strlen(azResult[1]));
  debug_print("verBak = %s\n", verBak);
  sqlite3_free_table(azResult);
  sqlite3_free(zErrMsg);
  sqlite3_close_v2(config_db);

  memset(ver, 0, 100);
  //从软件版本txt读取软件版本
  read_version_from_txt(ver);
  debug_print("version = %s \n", ver);

  
  /* 创建基础信息数据库 */
  //err = sqlite3_open("/home/meican/base_config.db",&config_db);
  err = sqlite3_open_v2("/home/meican/base_config.db", &config_db, SQLITE_OPEN_READWRITE, NULL);
  if(err) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return err;
  }
  sprintf(tempdata, "update config set softWare_bak='%s', jobId='%s', otaResult='ok' where v2id>=0", ver, jobid);//
  debug_print("tempdata = %s \n", tempdata);
  err = sqlite3_exec(config_db, tempdata, NULL, NULL, &zErrMsg);
  sqlite3_close_v2(config_db);

  if(strcmp(ver, verBak) == 0) {
    debug_print("已是最新版本无需更新\n");
    return 0xff;
  }
  return err;
}

/*==================================================================================
* 函 数 名： sqlite_update_versionBak_config_db
* 参    数： 
* 功能描述:  修改配置数据库软件备份临时版本，固件更新完下次启动时读取跟软件版本字段比较
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-05-25 //
==================================================================================*/
char jobid[200];
char* sqlite_read_versionBak_config_db(void)
{
  int err;
  int nrow,ncolumn;
  char tempdata[500];
  
  char **azResult; //是 char ** 类型，两个*号
  sqlite3 *config_db =NULL;

  memset(jobid, 0, 200);
  /* 打开基础信息数据库 */
  err = sqlite3_open_v2("/home/meican/base_config.db", &config_db, SQLITE_OPEN_READONLY, NULL);
  if(err) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return ;
  }
  //查找shadow名字
  char *sql = "select jobId from config";
  err = sqlite3_get_table(config_db, sql, &azResult, &nrow, &ncolumn, &zErrMsg);
  if(err) {
    debug_print("Can't select jobId: %s\n", sqlite3_errmsg(config_db));
    sqlite3_free_table(azResult);
    sqlite3_free(zErrMsg);
    sqlite3_close_v2(config_db);
    return ;
  }
  memcpy(jobid, azResult[1], strlen(azResult[1]));
  debug_print("jobID = %s\n", jobid);
  sqlite3_free_table(azResult);
  sqlite3_free(zErrMsg);
  sqlite3_close_v2(config_db);
  return jobid;
}

/*==================================================================================
* 函 数 名： sqlite_read_uuid_config_db
* 参    数： 
* 功能描述:  配置数据库读取UUID
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-05-25 //
==================================================================================*/
char shadow_uuid[200];
char* sqlite_read_uuid_config_db(void)
{
  int err;
  int nrow,ncolumn;
  char tempdata[500];
  
  char **azResult; //是 char ** 类型，两个*号
  sqlite3 *config_db =NULL;

  memset(shadow_uuid, 0, 200);
  /* 打开基础信息数据库 */
  err = sqlite3_open_v2("/home/meican/base_config.db", &config_db, SQLITE_OPEN_READONLY, NULL);
  if(err) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return ;
  }
  //查找shadow名字
  char *sql = "select shadow_id from config";
  err = sqlite3_get_table(config_db, sql, &azResult, &nrow, &ncolumn, &zErrMsg);
  if(err) {
    debug_print("Can't select shadow_id: %s\n", sqlite3_errmsg(config_db));
    sqlite3_free_table(azResult);
    sqlite3_free(zErrMsg);
    sqlite3_close_v2(config_db);
    return ;
  }
  memcpy(shadow_uuid, azResult[1], strlen(azResult[1]));
  debug_print("shadow_uuid = %s\n", shadow_uuid);
  sqlite3_free_table(azResult);
  sqlite3_free(zErrMsg);
  sqlite3_close_v2(config_db);
  return shadow_uuid;
}

/*================================================================================================================================
* 函 数 名： sqlite_read_meican_indent_code
* 参    数： 
* 功能描述:  从配置数据库读取美餐餐盘识别码
* 返 回 值： 成功返回识别码，失败返回 -1
* 备    注： 
* 作    者： lc
* 创建时间： 2021-05-27 
===================================================================================================================================*/
int sqlite_read_meican_indent_code(void)
{
  int err = -1,Indent_code = -1;
  int nrow,ncolumn;
  char *errmsg = NULL;
  char **azResult; //是 char ** 类型，两个*号
  sqlite3 *config_db =NULL;

  /* 打开基础信息数据库 */
  //err = sqlite3_open("/home/meican/base_config.db",&config_db);
  err = sqlite3_open_v2("/home/meican/base_config.db", &config_db, SQLITE_OPEN_READONLY, NULL);
  if(err) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return Indent_code;
  }
  //查找美餐餐盘识别码
  char *sql = "select indent_code from config";
  err = sqlite3_get_table(config_db, sql, &azResult, &nrow, &ncolumn, &zErrMsg);
  if(err) {
    debug_print("Can't select Indent_code: %s\n", sqlite3_errmsg(config_db));
    sqlite3_free_table(azResult);
    sqlite3_free(zErrMsg);
    sqlite3_close_v2(config_db);
    return Indent_code;
  }
  // for(i=0;i<(nrow+1)*ncolumn;i++)
  // {
  //   debug_print("azResult[%d]=%s\n",i,azResult[i]);
  // }
  Indent_code = atoi(azResult[1]);//识别码赋值
  debug_print("Indent_code = %d\n",Indent_code);
  sqlite3_free_table(azResult);
  sqlite3_free(zErrMsg);
  sqlite3_close_v2(config_db);
  return Indent_code;
}

/*================================================================================================================================
* 函 数 名： sqlite_read_menu_ver
* 参    数： 
* 功能描述:  从配置数据库读取当前菜单版本（时间戳）
* 返 回 值： 成功返回菜单版本，失败返回 -1
* 备    注： 
* 作    者： lc
* 创建时间： 2021-05-27 
===================================================================================================================================*/
int64_t sqlite_read_menu_ver(void)
{
  int err =-1;
  int64_t menu_ver = -1;
  int nrow,ncolumn;
  char *errmsg = NULL;
  char **azResult; //是 char ** 类型，两个*号
  sqlite3 *config_db =NULL;

  /* 打开基础信息数据库 */
 // err = sqlite3_open("/home/meican/base_config.db",&config_db);
  err = sqlite3_open_v2("/home/meican/base_config.db",&config_db,SQLITE_OPEN_READONLY, NULL);
  if( err ) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return menu_ver;
  }
  //查找美餐餐盘识别码
  char *sql = "select menu_ver from config";
  err = sqlite3_get_table(config_db, sql, &azResult, &nrow, &ncolumn, &zErrMsg);
  if( err ) {
    debug_print("Can't select menu_ver: %s\n", sqlite3_errmsg(config_db));
    sqlite3_free_table(azResult);
    sqlite3_free(zErrMsg);
    sqlite3_close_v2(config_db);
    return menu_ver;
  }

  menu_ver = S64(azResult[1]);//字符串转int64
  debug_print("menu_ver = %lld\n",menu_ver);
  sqlite3_free_table(azResult);
  sqlite3_free(zErrMsg);
  sqlite3_close_v2(config_db);
  return menu_ver;
}

/*================================================================================================================================
* 函 数 名： sqlite_read_shandow_config_message
* 参    数： 
* 功能描述:  从配置数据库读取shadow配置信息
* 返 回 值： 成功返回菜单版本，失败返回 -1
* 备    注： 
* 作    者： lc
* 创建时间： 2021-05-27 
===================================================================================================================================*/
static char namebuf[200];
static char idbuf[200];
C_ShadowMsgSt sqlite_read_shandow_config_message(void)
{
  int err =-1;
  int64_t menu_ver = -1;
  int nrow,ncolumn;
  char *errmsg = NULL;
  char **azResult; //是 char ** 类型，两个*号
  sqlite3 *config_db =NULL;
  C_ShadowMsgSt pShadow;

  /* 打开基础信息数据库 */
  //err = sqlite3_open("/home/meican/base_config.db",&config_db);
  err = sqlite3_open_v2("/home/meican/base_config.db",&config_db,SQLITE_OPEN_READONLY, NULL);
  if( err ) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return pShadow;
  }
  //查找shadow名字
  char *sql = "select shadow_name from config";
  err = sqlite3_get_table(config_db, sql, &azResult, &nrow, &ncolumn, &zErrMsg);
  if( err ) {
    debug_print("Can't select shadow_name: %s\n", sqlite3_errmsg(config_db));
    sqlite3_free_table(azResult);
    sqlite3_free(zErrMsg);
    sqlite3_close_v2(config_db);
    return pShadow;
  }
  pShadow.name = azResult[1];//shadow 名字
  debug_print("shadow_name = %s\n",pShadow.name);

  //查找shadow  clientid
  sql = "select shadow_id from config";
  err = sqlite3_get_table(config_db, sql, &azResult, &nrow, &ncolumn, &zErrMsg);
  if( err ) {
    debug_print("Can't select shadow_id: %s\n", sqlite3_errmsg(config_db));
    sqlite3_free_table(azResult);
    sqlite3_free(zErrMsg);
    sqlite3_close_v2(config_db);
    return pShadow;
  }
  pShadow.clientid = azResult[1];//shadow 名字
  memcpy(idbuf,pShadow.clientid,sizeof(pShadow.clientid));
  debug_print("shadow_id = %s\n",pShadow.clientid);

  sqlite3_free_table(azResult);
  sqlite3_free(zErrMsg);
  sqlite3_close_v2(config_db);

  return pShadow;
}

/*==================================================================================
* 函 数 名： sqlite_update_shadowMsg_to_config_db
* 参    数： 
* 功能描述:  修改配置数据库shadow信息
* 返 回 值： None
* 备    注： 修改成功返回0
* 作    者： lc
* 创建时间： 2021-05-25 //
==================================================================================*/
int sqlite_update_shadowMsg_to_config_db(C_ShadowMsgSt pdev)
{
  int err;
  char tempdata[500];
  sqlite3 *config_db =NULL;

  /* 创建基础信息数据库 */
 // err = sqlite3_open("/home/meican/base_config.db",&config_db);
  err = sqlite3_open_v2("/home/meican/base_config.db",&config_db,SQLITE_OPEN_READWRITE, NULL);
  if( err ) {
    debug_print("Can't open database: %s\n", sqlite3_errmsg(config_db));
    sqlite3_close_v2(config_db);
    return err;
  }
  sprintf(tempdata,"update config set shadow_name='%s',shadow_id='%s' where v2id>=0",pdev.name,pdev.clientid);//
  debug_print("tempdata = %s \n",tempdata);
  err = sqlite3_exec(config_db,tempdata,NULL,NULL,&zErrMsg);
  sqlite3_close_v2(config_db);
  return err;
}


//sqlite 测试
void sqlite_test(void)
{
  char premenu[100] = "三级菜单" ;
  char nextmenu[100] = "";
  char context[100] = "西红柿鸡蛋";
  char spell[100] = "X"; 
  int grade = 3;
  int dish_id,i;
  dishMsgSt dishMsg;
  C_DevMsgSt pdev;

  //菜单测试
  // for(i=0;i<10;i++)
  // {
  //   sqlite_insert_menu_db(1, premenu, nextmenu, grade, context, spell, i,0);
  //   sqlite_insert_menu_db(2, premenu, nextmenu, grade, context, spell, i,0);
  //   sqlite_insert_menu_db(3, premenu, nextmenu, grade, context, spell, i,1200);
  // }  
  //写盘信息
  //sqlite_insert_menu_db(4, premenu, nextmenu, grade, context, spell, i,1200);

  //修改设备信息
  sprintf(pdev.uuid,"%s","12467b167cad572d5bd4ccf53377b641");
  sprintf(pdev.sn,"%s","DM-2901-050006");
  pdev.id = 11000;
  sqlite_update_devMsg_to_config_db( pdev);

  // //读取写盘信息
  // dishMsg = sqlite_read_msg_dishmenu();
  // if(dishMsg.res == SQLITE_OK )
  // {
  //   debug_print("dish price = %d\n", dishMsg.price);
  // }
}

int sqlite_open_test()
{
  int food_id = 0;
  char context[100] = "西红柿鸡蛋";
  qtdata_t mSndMsg;
  dishMsgSt dishMsg;

  sqlite_write_food_menu_db(context,food_id,0);
  dishMsg = sqlite_read_writePlateMsg_from_dishmenu();
  if(dishMsg.res == SQLITE_OK)
  {
    mSndMsg.datalen = 3;
    mSndMsg.cmd = 1;
    mSndMsg.data[0] = 0;//
    qt_push_data_to_msg(mSndMsg);//发送写盘状态到发送队列
  } else {
    debug_print("sqlite_read_writePlateMsg_from_dishmenu fail \n");
  }
}
