include "Instructions.dfy"

class Kernel{

    method exec(instruction:Instruction) {
        print "Executing instruction in kernel\n";
    }

    constructor () {
    }
}