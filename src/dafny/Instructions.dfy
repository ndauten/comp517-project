datatype Instruction = 
    Write(value:char, addr:int) 
    | Read(addr:int)