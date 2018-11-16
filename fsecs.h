/*
 * Function timers
 */
typedef void (*ftimer_test_funct)(void *);
typedef void (*fsecs_test_funct)(void *);

/* Estimate the running time of f(argp) using gettimeofday
   Return the average of n runs */
double ftimer_gettod(ftimer_test_funct f, void *argp, int n);

void init_fsecs(void);
double fsecs(fsecs_test_funct f, void *argp);
