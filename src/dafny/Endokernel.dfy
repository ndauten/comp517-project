// include "Capability.dfy"
// include "Endoprocess.dfy"
// include "Kernel.dfy"

// class Endokernel {
//     var capabilities: map<Capability, Endoprocess>
//     var endoprocesses: map<int, Endoprocess>
//     var instructionMap: map<string, Capability>
//     var nextPid:int;
//     var kernel:Kernel;

//     method createEndoprocess(capability:Capability, instruction:string) returns (endoprocess:Endoprocess) modifies this {
//         endoprocess := new Endoprocess(capability.subspace, instruction, this);
//         this.capabilities := capabilities[capability := endoprocess];
//         this.endoprocesses := this.endoprocesses[this.nextPid := endoprocess];
//         this.nextPid := nextPid + 1;
//     }

//     method trap(instruction:string) modifies this {
//         if (instruction !in instructionMap){
//            print "Trap error: no policy for this instruction";
//         } 
//         else {
//             var capability:Capability := instructionMap[instruction];
//             var endoprocess:Endoprocess;
//             if (capability !in capabilities) {
//                 endoprocess := createEndoprocess(capability, instruction);
//             } else {
//                 endoprocess := capabilities[capability];
//             }
//             endoprocess.exec(instruction);
//         }
//     }

//     method trapEndoprocess(instruction:string) modifies this {
//         kernel.exec(instruction);
//     }


//     constructor() {
//         this.nextPid := 0;
//         this.capabilities := map[];
//         this.endoprocesses := map[];
//         this.instructionMap := map[];
//     }
// }