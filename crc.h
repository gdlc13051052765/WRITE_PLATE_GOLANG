#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include <sys/ioctl.h>
#include <sys/types.h>

//工装测试CRC数据效验
int crc16_calc(const char* buf, char len);

void crc16_test(void);