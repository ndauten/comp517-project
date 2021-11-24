include "Capability.dfy"
include "Kernel.dfy"
include "Instructions.dfy"

class Endokernel {
    var capabilities: map<Capability, Endoprocess>
    var endoprocesses: map<int, Endoprocess>
    var instructionMap: map<Instruction, Capability>
    var nextPid:int;
    var kernel:Kernel;

    method createEndoprocess(capability:Capability, instruction:Instruction) returns (endoprocess:Endoprocess) modifies this {
        endoprocess := new Endoprocess(this.nextPid, capability.subspace, instruction, this);
        this.capabilities := capabilities[capability := endoprocess];
        this.endoprocesses := this.endoprocesses[this.nextPid := endoprocess];
        this.nextPid := nextPid + 1;
    }

    method trap(instruction:Instruction) modifies this  { 
        if (instruction !in instructionMap){
           print "trap error: no policy for this instruction\n";
        } 
        else {
            var capability:Capability := instructionMap[instruction];
            var endoprocess:Endoprocess;
            if (capability !in capabilities) {
                endoprocess := createEndoprocess(capability, instruction);
            } else {
                endoprocess := capabilities[capability];
            }
            
            print "Trapping instruction";
            print instruction;
            print "from Process in Endokernel\n";
            endoprocess.exec(instruction);
        }
    }

    method trapEndoprocess(instruction:Instruction, endoId:int) {
        // Verifying if endoprocess has correct access rights to execute this instruction
        if (instruction !in instructionMap){
           print "trapEndoprocess error: no policy for this instruction\n";
        }  
        else {
            var capability := instructionMap[instruction];
            if (capability !in capabilities) {
                print "trapEndoprocess error: this endoprocess has not the required rights for such instruction\n";
            } else {
                var endoprocessExpected := capabilities[capability];
                if ( endoId !in endoprocesses) {
                    print "trapEndoprocess error: unknown endoprocess\n";
                }
                else {
                    var endoprocessTrapped := endoprocesses[endoId];
                    if (endoprocessTrapped != endoprocessExpected) {
                        print "trapEndoprocess error: unknown endoprocess\n";
                    }
                    else {
                        print "Trapping back instruction from Endoprocess in Endokernel\n";
                        kernel.exec(instruction);
                    }
                }
            }
        }
    }


    constructor(kernel:Kernel) {
        this.nextPid := 0;
        this.capabilities := map[];
        this.endoprocesses := map[];
        var capability:Capability := new Capability();
        var instruction:Instruction := Write('a', 0);
        this.instructionMap := map[instruction := capability];
        this.kernel := kernel;
    }
}

class Endoprocess {
    var id:int;
    var memorySpace:seq<int>
    var instructions: Instruction
    var endokernel:Endokernel;

    constructor(id:int, memorySpace:seq<int>, instructions:Instruction, endokernel:Endokernel) {
        this.id := id;
        this.memorySpace := memorySpace;
        this.instructions := instructions;
        this.endokernel := endokernel;
    }

    method exec(instruction:Instruction)  {
        print "Executing instruction in Endoprocess\n";
        endokernel.trapEndoprocess(instruction, this.id);
    }
}