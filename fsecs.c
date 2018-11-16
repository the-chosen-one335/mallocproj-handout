/****************************
 * High-level timing wrappers
 ****************************/
#include <stdio.h>
#include <sys/time.h>
#include "fsecs.h"
#include "config.h"

static double Mhz;  /* estimated CPU clock frequency */

extern int verbose; /* -v option in mdriver.c */

/*
 * ftimer_gettod - Use gettimeofday to estimate the running time of
 * f(argp). Return the average of n runs.
 */
double ftimer_gettod(ftimer_test_funct f, void *argp, int n)
{
    int i;
    struct timeval stv, etv;
    double diff;

    gettimeofday(&stv, NULL);
    for (i = 0; i < n; i++)
	f(argp);
    gettimeofday(&etv,NULL);
    diff = 1E3*(etv.tv_sec - stv.tv_sec) + 1E-3*(etv.tv_usec-stv.tv_usec);
    diff /= n;
    return (1E-3*diff);
}


/*
 * init_fsecs - initialize the timing package
 */
void init_fsecs(void)
{
    Mhz = 0; /* keep gcc -Wall happy */

    if (verbose)
	printf("Measuring performance with gettimeofday().\n");
}

/*
 * fsecs - Return the running time of a function f (in seconds)
 */
double fsecs(fsecs_test_funct f, void *argp)
{
    return ftimer_gettod(f, argp, 10);
}

