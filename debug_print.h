#ifndef  __DEBUG_PRINT_H
#define  __DEBUG_PRINT_H

#define EN_DEBUG  (0)   //1:调试          0:正常运行

#if EN_DEBUG == 0
  #define debug_print		printf
#else
  #define debug_print	 	
#endif

#endif