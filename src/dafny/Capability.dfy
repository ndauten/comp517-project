

class Capability {
    var subspace: seq<int>
    var stack: seq<int>
    var files: seq<string>
    var entries: seq<string>

    constructor () {
        subspace := [];
        stack := [];
        files := [];
        entries := [];
    }

}