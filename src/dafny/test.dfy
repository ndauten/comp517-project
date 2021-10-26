include "Process.dfy"
include "Endo.dfy"
include "Kernel.dfy"

class Test {

    method testProcess1() {
        // Example of a simple execution of the Endokernel abstraction
        var kernel:Kernel := new Kernel();
        var endokernel:Endokernel := new Endokernel(kernel);
        var p:Process := new Process(0, [0,1,2,3], ["write(0,a)"], endokernel);
        p.entryProcess(endokernel);
    }

    method testProcess2() {
        // Example of a simple execution of the Endokernel abstraction that is not handled
        var kernel:Kernel := new Kernel();
        var endokernel:Endokernel := new Endokernel(kernel);
        var p:Process := new Process(0, [0,1,2,3], ["read(0,a)"], endokernel);
        p.entryProcess(endokernel);
    }


    method Main()  {
        testProcess1();
        //testProcess2();
    }
}