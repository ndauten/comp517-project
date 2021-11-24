include "Endo.dfy"

class Thread {
    var tid:int;
    var pc:int;
    var sp:int;
    var instructions:seq<string>;
    var endokernel:Endokernel;

    constructor (tid:int, pc:int, sp:int, instructions:seq<string>, endokernel:Endokernel)
    ensures this.endokernel == old(endokernel)
     {
        this.tid := tid;
        this.pc := pc;
        this.sp := sp;
        this.instructions := instructions;
        this.endokernel := endokernel;
    }

    method exec() modifies this, endokernel {
        if (0 <= pc < |instructions|) {
            print "Executing instruction " + instructions[pc] + " in Process\n";
            this.endokernel.trap(instructions[pc]);
            pc := pc + 1;
        }
    }

}