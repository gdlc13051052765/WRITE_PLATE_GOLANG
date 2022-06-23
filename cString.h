
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

/*从字符串的左边截取n个字符*/
char * cStringLeft(char *dst, char *src, int n);

/*从字符串的中间截取n个字符*/
char * cStringMid(char *dst, char *src, int n, int m); /*n为长度，m为位置*/

/*从字符串的右边截取n个字符*/
char * cStringRight(char *dst, char *src, int n);
/************************************************************************/
/* 删除字符串中指定字符 */
/************************************************************************/
void del_char(char* str, char ch);