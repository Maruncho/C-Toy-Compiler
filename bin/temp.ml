
(*Global variables prohibit multithreaded code execution, but passing label object as arguments to functions is too much work for someone who doesn't plan to go multithreaded.*)

let tmpNum = ref 0
let newTemp() = (let t = "tmp." ^ (string_of_int (!tmpNum)) in let () = tmpNum := !tmpNum + 1 in t)

