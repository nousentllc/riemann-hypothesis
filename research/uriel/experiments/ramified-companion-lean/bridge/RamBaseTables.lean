import RamBaseData
namespace RamBase
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem transition0 : checks (fun k => decide (step (fun j => row0 (repNo j)) (encode (decode (repCode k))) = row1 k)) 58 = true := by decide +kernel
theorem transition1 : checks (fun k => decide (step (fun j => row1 (repNo j)) (encode (decode (repCode k))) = row2 k)) 58 = true := by decide +kernel
theorem transition2 : checks (fun k => decide (step (fun j => row2 (repNo j)) (encode (decode (repCode k))) = row3 k)) 58 = true := by decide +kernel
theorem transition3 : checks (fun k => decide (step (fun j => row3 (repNo j)) (encode (decode (repCode k))) = row4 k)) 58 = true := by decide +kernel
theorem transition4 : checks (fun k => decide (step (fun j => row4 (repNo j)) (encode (decode (repCode k))) = row5 k)) 58 = true := by decide +kernel
theorem transition5 : checks (fun k => decide (step (fun j => row5 (repNo j)) (encode (decode (repCode k))) = row6 k)) 58 = true := by decide +kernel
end RamBase
