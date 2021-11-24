include "Endo.dfy"
include "Thread.dfy"

class Process {
    var pid:int;
    var memorySpace: seq<int>; 
    var instructions: seq<string>;
    var endokernel: Endokernel;
    var thread: Thread;

    constructor(pid:int, memorySpace:seq<int>, instructions:seq<string>, endokernel:Endokernel)
    ensures this.endokernel == old(endokernel)
    {
        this.pid := pid;
        this.memorySpace := memorySpace;
        this.instructions := instructions;
        this.endokernel := endokernel;
        this.thread := new Thread(0, 0, 0, instructions, endokernel);
    }

    method exec() modifies this, thread, thread.endokernel {
        thread.exec();
    }

}
