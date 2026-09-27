
fun ptime(date : date, cal : calendar) : <parse,utc> time
  one-of("T ")
  val hour = num(2)
  colon()
  val min = optional(0){num(2)}
  colon()
  val secs = optional(ddouble/zero) { val s = num(2) 
                                      val f = optional(""){ one-of(".,"); digits() }
                                      (s.ddouble + (if f.is-empty then zero else ("0." ++ f).parse-ddouble.default(zero))) } 
  val tzone = choose([
                { val sign = one-of("+-")
                  val tzhour = num(2)
                  colon()
                  val tzmin = num(2)
                  tz-fixed( if sign=='-' then tzhour.negate else tzhour, tzmin )
                }, 
                { optional('Z'){ char('Z') }; tz-utc }
              ])
  val clk = Clock(hour,min,secs)
  time(date,clk,tz=tzone,cal=cal)