import compiler/syntax/format
import std/os/path

fun main()
  with val format-opts = FormattingOptions()
  file/format("compiler/common/failure.kk".path)
  file/format("compiler/syntax/format.kk".path)