#ifndef __MM_H_
#define __MM_H_
#include <stdio.h>

extern int mm_init (void);
extern void *mm_malloc (size_t size);
extern void mm_free (void *ptr);

/*
 * mm_realloc - You DO NOT need to implement this function
 */
/* void *mm_realloc(void *ptr, size_t size) { return NULL;} */

/*
 * Students work in groups of one, two or three members. Groups
 * enter their group number, personal names and CityU emails in
 * a struct of this type in their mm.c file.
 */
typedef struct {
    char *groupno;  	/* Project group number*/
    char *name1;    	/* Full name of first member */
    char *email1;      	/* Email of first member */
    char *name2;    	/* Full name of second member (if any) */
    char *email2;      	/* Email of second member */
    char *name3;    	/* Full name of third member (if any) */
    char *email3;      	/* Email of third member */
} group_t;

extern group_t group;
#endif /* __MM_H_ */
