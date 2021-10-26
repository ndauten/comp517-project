include "Endo.dfy"

class Process {
    var pid:int;
    var memorySpace: seq<int>; 
    var instructions: seq<string>;
    var endokernel: Endokernel;
    var pc: int;

    constructor(pid:int, memorySpace:seq<int>, instructions:seq<string>, endokernel:Endokernel)
    {
        this.pid := pid;
        this.memorySpace := memorySpace;
        this.instructions := instructions;
        this.endokernel := endokernel;
        this.pc := 0;
    }

    method exec() modifies this, endokernel {
        if (0 <= pc < |instructions|) {
            print "Executing instruction " + instructions[pc] + " in Process\n";
            this.endokernel.trap(instructions[pc]);
            pc := pc + 1;
        }
    }

    method entryProcess(endokernel:Endokernel) modifies this, endokernel {
        // Example of a simple execution of the Endokernel abstraction
        this.endokernel := endokernel;
        this.exec();
    }

}