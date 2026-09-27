
function kk_bslice_assign(original, start, newSlice) {
  const result = original.slice() // Copy
  result.set(kk_bslice_bytes(newSlice), start)
  return result;
}

function kk_bslice_bytes(oldSlice) {
  return oldSlice.backing_bytes.slice(oldSlice.start, oldSlice.len + oldSlice.start)
}