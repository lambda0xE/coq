let rec add_vectors vector1 vector2 =
  match (vector1, vector2) with
  | ([], []) -> []
  | (hd1::tl1, hd2::tl2) -> (hd1 + hd2) :: add_vectors tl1 tl2
  | _ -> failwith "Vectors have different lengths"

let vector1 = [1; 2; 3]
let vector2 = [4; 5; 6]

let result = add_vectors vector1 vector2
