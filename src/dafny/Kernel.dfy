include "Instructions.dfy"
include "Syscalls.dfy"

class Kernel{

    method exec(syscall:Syscall) {
        print "Executing syscall ";
        print syscall;
        print " in kernel\n";
    }

    constructor () {
    }
}