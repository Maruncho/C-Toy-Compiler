
(*Global variables prohibit multithreaded code execution, but passing label object as arguments to functions is too much work for someone who doesn't plan to go multithreaded.*)

let lblNum = ref 0
let newLbl() = let t = ".L" ^ (string_of_int (!lblNum)) in let () = lblNum := !lblNum + 1 in t

let roCnt = ref 0
let newRo() = let lbl = ".RO_"^(string_of_int !roCnt) in let () = roCnt := !roCnt + 1 in lbl



let compare x y = Int64.compare (Int64.bits_of_float x) (Int64.bits_of_float y)
module MapDouble = Map.Make(struct type t = float let compare = compare end)

let doubleConsts : string MapDouble.t ref = ref MapDouble.empty
let getLabelDouble num = match MapDouble.find_opt num !doubleConsts with
    | None -> let lbl = newRo() in
              let () = doubleConsts := MapDouble.add num lbl !doubleConsts in
              lbl
    | Some lbl -> lbl
let labelDoubleFlushToList() = let r = MapDouble.to_list !doubleConsts in
                               let () = doubleConsts := MapDouble.empty in r


module MapString = Map.Make(struct type t = string let compare = String.compare end)

let stringConsts : string MapString.t ref = ref MapString.empty
let getLabelString str = match MapString.find_opt str !stringConsts with
    | None -> let lbl = newRo() in
              let () = stringConsts := MapString.add str lbl !stringConsts in
              lbl
    | Some lbl -> lbl
let labelStringFlushToList() = let r = MapString.to_list !stringConsts in
                               let () = stringConsts := MapString.empty in r
