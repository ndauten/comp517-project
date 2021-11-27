datatype Syscall = 
    Write(value:char, addr:int) 
    | Read(addr:int)