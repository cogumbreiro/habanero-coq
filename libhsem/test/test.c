#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "hsem.h"

int main(int argc, char **argv)
{
  struct habanero_checks* s = habanero_checks_new();
  
  // Example where we initalize, create a task, and remove that task
  
  assert(habanero_checks_add(s, (habanero_action) {
    .task = 1,
    .op = INIT,
    .id = 1,
    .time = 1,
    .arg = 0
  }));

  assert(habanero_checks_add(s, (habanero_action) {
    .task = 1,
    .op = BEGIN_TASK,
    .id = 1,
    .time = 2,
    .arg = 2
  }));

  assert(habanero_checks_add(s, (habanero_action) {
    .task = 2,
    .op = BEGIN_FINISH,
    .id = 2,
    .time = 0,
    .arg = 0
  }));
  
  assert(habanero_checks_add(s, (habanero_action) {
    .task = 2,
    .op = END_FINISH,
    .id = 2,
    .time = 1,
    .arg = 0
  }));

  assert(habanero_checks_add(s, (habanero_action) {
    .task = 1,
    .op = END_TASK,
    .id = 1,
    .time = 3,
    .arg = 0
  }));
  habanero_checks_free(s);
  puts("All tests passed!");
  return 0;
}
