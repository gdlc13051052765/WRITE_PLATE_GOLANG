#include <stdio.h>
#include <string.h>

/*从字符串的左边截取n个字符*/
char * cStringLeft(char *dst, char *src, int n)
{
    char *p = src;
    char *q = dst;
    int len = strlen(src);
    if(n>len) n = len;
    /*p += (len-n);*/   /*从右边第n个字符开始*/
    while(n--) *(q++) = *(p++);
    *(q++)='\0'; /*有必要吗？很有必要*/
    return dst;
}

/*从字符串的中间截取n个字符*/
char * cStringMid(char *dst, char *src, int n, int m) /*n为长度，m为位置*/
{
    char *p = src;
    char *q = dst;
    int len = strlen(src);
    if(n>len) n = len-m;    /*从第m个到最后*/
    if(m<0) m=0;    /*从第一个开始*/
    if(m>len) return NULL;
    p += m;
    while(n--) *(q++) = *(p++);
    *(q++)='\0'; /*有必要吗？很有必要*/
    return dst;
}

/*从字符串的右边截取n个字符*/
char * cStringRight(char *dst, char *src, int n)
{
    char *p = src;
    char *q = dst;
    int len = strlen(src);
    if(n>len) n = len;
    p += (len-n);   /*从右边第n个字符开始*/
    while(*(q++) = *(p++));
    return dst;
}
/************************************************************************/
/* 删除字符串中指定字符 */
/************************************************************************/
void del_char(char* str, char ch)
{
    char *p = str;
    char *q = str;
    while(*q)
    {
        if (*q !=ch)
        {
            *p++ = *q;
        }
        q++;
    }
    *p='\0';
}
