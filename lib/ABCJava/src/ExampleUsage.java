import java.math.BigInteger;
import java.util.Map;
import java.util.Map.Entry;

import vlab.cs.ucsb.edu.DriverProxy;
import vlab.cs.ucsb.edu.DriverProxy.Option;

public class ExampleUsage {

  public static void main(String[] args) {

    DriverProxy abcDriver = new DriverProxy();
    
    
    String handle = "(declare-fun h () Int)(declare-fun l () Int)(assert (<= h 1023))(assert (>= h 0))(assert (<= l 1023))(assert (>= l 0))(assert (or (and (> 1023 ( +  l 50))(<= 1022 ( +  l 50))(<= 1000 ( +  l 50))(<= 998 ( +  l 50))(<= 981 ( +  l 50))(>= 981 l)(< h l)(< 889 l)(< 881 l)(< 823 l)(< 792 l)(< 675 l)(< 654 l)(< 576 l)(< 543 l)(< 542 l)(< 456 l)(<= h 981)(> h 889)(> h 881)(> h 823)(> h 792)(> h 675)(> h 654)(> h 576)(> h 542)(> h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (>= 9 l)(< 5 l)(> 456 ( +  l 50))(>= 456 l)(<= h 675)(> h 654)(> h 576)(> h 542)(> h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (>= 998 l)(< 981 l)(< 889 l)(< h l)(< 881 l)(< 823 l)(< 792 l)(< 675 l)(< 654 l)(< 576 l)(< 543 l)(< 542 l)(< 456 l)(<= h 889)(> h 881)(> h 823)(> h 792)(> h 675)(> h 654)(> h 576)(> h 542)(> h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (> 1023 ( +  l 50))(<= 1022 ( +  l 50))(<= 1000 ( +  l 50))(<= 998 ( +  l 50))(<= 981 ( +  l 50))(>= 981 l)(< 889 l)(< 881 l)(< 823 l)(< 792 l)(< 675 l)(< 654 l)(< 576 l)(< 543 l)(< 542 l)(< 456 l)(<= h 312)(> h 297)(> h 213)(> h 189)(> h 154)(> h 123)(> h 76)(> h 67)(> h 15)(> h 13)(> h 9)(> h 5)(<= h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (>= 998 l)(< 981 l)(< 889 l)(< 881 l)(< 823 l)(< 792 l)(< 675 l)(< 654 l)(< 576 l)(< 543 l)(< 542 l)(< 456 l)(<= h 297)(> h 213)(> h 189)(> h 154)(> h 123)(> h 76)(> h 67)(> h 15)(> h 13)(> h 9)(> h 5)(<= h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (> 76 ( +  l 50))(<= h ( +  l 50))(<= 67 ( +  l 50))(>= 67 l)(< 15 l)(< 13 l)(< 9 l)(< 5 l)(> 456 ( +  l 50))(>= 456 l)(<= h 76)(> h 67)(> h 15)(> h 13)(> h 9)(> h 5)(<= h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (<= 576 ( +  l 50))(<= 543 ( +  l 50))(<= 542 ( +  l 50))(>= 542 l)(< 456 l)(<= h 5)(<= h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (<= h ( +  l 50))(<= 889 ( +  l 50))(<= 881 ( +  l 50))(>= 881 l)(< 823 l)(< 792 l)(< 675 l)(< 654 l)(< 576 l)(< 543 l)(< 542 l)(< 456 l)(<= h 981)(> h 889)(> h 881)(> h 823)(> h 792)(> h 675)(> h 654)(> h 576)(> h 542)(> h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (>= 9 l)(< 5 l)(> 456 ( +  l 50))(>= 456 l)(<= h 123)(> h 76)(> h 67)(> h 15)(> h 13)(> h 9)(> h 5)(<= h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (> h ( +  l 50))(>= 312 l)(< 297 l)(< 213 l)(< 189 l)(< 154 l)(< 123 l)(< 76 l)(< 67 l)(< 15 l)(< 13 l)(< 9 l)(< 5 l)(> 456 ( +  l 50))(>= 456 l)(> h 345)(> h 328)(> h 321)(> h 312)(> h 297)(> h 213)(> h 189)(> h 154)(> h 123)(> h 76)(> h 67)(> h 15)(> h 13)(> h 9)(> h 5)(<= h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (> 328 ( +  l 50))(<= 321 ( +  l 50))(<= 312 ( +  l 50))(<= 297 ( +  l 50))(>= 297 l)(< 213 l)(< 189 l)(< 154 l)(< 123 l)(< 76 l)(< 67 l)(< 15 l)(< h l)(< 13 l)(< 9 l)(< 5 l)(> 456 ( +  l 50))(>= 456 l)(<= h 15)(> h 13)(> h 9)(> h 5)(<= h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))))(check-sat)";
    String high_cons = "(assert (or (and (> 823 ( +  9 50))(<= 792 ( +  9 50))(<= h ( +  9 50))(>= h 9)(< 675 9)(< 654 9)(< 576 9)(< 543 9)(< 542 9)(< 456 9)(<= h 792)(> h 675)(> h 654)(> h 576)(> h 542)(> h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (>= 1000 9)(< 998 9)(< 981 9)(< 889 9)(< 881 9)(< 823 9)(< 792 9)(< 675 9)(< 654 9)(< 576 9)(< 543 9)(< 542 9)(< 456 9)(<= h 67)(> h 15)(> h 13)(> h 9)(> h 5)(<= h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (> 328 ( +  9 50))(<= 321 ( +  9 50))(<= 312 ( +  9 50))(<= 297 ( +  9 50))(>= 297 9)(< 213 9)(< 189 9)(< 154 9)(< 123 9)(< 76 9)(< 67 9)(< 15 9)(< 13 9)(< 9 9)(< 5 9)(> 456 ( +  9 50))(>= 456 9)(<= h 981)(> h 889)(> h 881)(> h 823)(> h 792)(> h 675)(> h 654)(> h 576)(> h 542)(> h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (>= 9 9)(< 5 9)(> 456 ( +  9 50))(>= 456 9)(<= h 1000)(> h 998)(> h 981)(> h 889)(> h 881)(> h 823)(> h 792)(> h 675)(> h 654)(> h 576)(> h 542)(> h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (>= 1000 9)(< 998 9)(< 981 9)(< 889 9)(< 881 9)(< 823 9)(< 792 9)(< 675 9)(< 654 9)(< 576 9)(< h 9)(< 543 9)(< 542 9)(< 456 9)(<= h 576)(> h 542)(> h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (>= 321 9)(< 312 9)(< 297 9)(< h 9)(< 213 9)(< 189 9)(< 154 9)(< 123 9)(< 76 9)(< 67 9)(< 15 9)(< 13 9)(< 9 9)(< 5 9)(> 456 ( +  9 50))(>= 456 9)(<= h 297)(> h 213)(> h 189)(> h 154)(> h 123)(> h 76)(> h 67)(> h 15)(> h 13)(> h 9)(> h 5)(<= h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (> 1022 ( +  9 50))(<= 1000 ( +  9 50))(<= 998 ( +  9 50))(<= 981 ( +  9 50))(>= 981 9)(< 889 9)(< 881 9)(< 823 9)(< 792 9)(< 675 9)(< 654 9)(< 576 9)(< 543 9)(< 542 9)(< 456 9)(<= h 76)(> h 67)(> h 15)(> h 13)(> h 9)(> h 5)(<= h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (> 1022 ( +  9 50))(<= 1000 ( +  9 50))(<= 998 ( +  9 50))(<= 981 ( +  9 50))(>= 981 9)(< 889 9)(< 881 9)(< 823 9)(< 792 9)(< 675 9)(< 654 9)(< h 9)(< 576 9)(< 543 9)(< 542 9)(< 456 9)(<= h 654)(> h 576)(> h 542)(> h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (<= 576 ( +  9 50))(<= 543 ( +  9 50))(<= 542 ( +  9 50))(>= 542 9)(< 456 9)(<= h 823)(> h 792)(> h 675)(> h 654)(> h 576)(> h 542)(> h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (>= 9 9)(< 5 9)(> 456 ( +  9 50))(>= 456 9)(<= h 328)(> h 321)(> h 312)(> h 297)(> h 213)(> h 189)(> h 154)(> h 123)(> h 76)(> h 67)(> h 15)(> h 13)(> h 9)(> h 5)(<= h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))(and (>= 321 9)(< 312 9)(< 297 9)(< 213 9)(< 189 9)(< 154 9)(< 123 9)(< 76 9)(< 67 9)(< 15 9)(< 13 9)(< 9 9)(< 5 9)(> 456 ( +  9 50))(>= 456 9)(<= h 889)(> h 881)(> h 823)(> h 792)(> h 675)(> h 654)(> h 576)(> h 542)(> h 456)(not (= h 15))(not (= h 67))(not (= h 1023))(not (= h 889))(not (= h 543))(not (= h 675))(not (= h 189))(not (= h 328))(not (= h 297))(not (= h 654))(not (= h 312))(not (= h 321))(not (= h 542))(not (= h 881))(not (= h 1000))(not (= h 13))(not (= h 9))(not (= h 154))(not (= h 5))(not (= h 76))(not (= h 1022))(not (= h 998))(not (= h 345))(not (= h 576))(not (= h 981))(not (= h 823))(not (= h 792))(not (= h 456))(not (= h 213))(not (= h 123)))))";
    String core_constraint = "(set-logic QF_S)\n"
        + "(declare-fun h () String)\n"
        + "(declare-fun l () String)\n"
        + "(assert (in h /[A-Z]{4,}/))\n"
        + "(assert (in l /[A-Z]{4,}/))\n"
        + "(assert (= (charAt h 0) (charAt l 0)))\n"
        + "(check-sat)";
    // solve initial constraint, 
    
    boolean result = abcDriver.isSatisfiable(handle);

    System.out.println("----------DONE CORE-----------");
    result = abcDriver.isSatisfiable2(high_cons,false);



    // System.out.println("----------DONE CORE-----------");
    // // get id of core constraint
    // String core_constraint_id = abcDriver.getCurrentID();

    // // from core constraint, we have two branches we want to build off of
    // String branch1 = "(assert (< l h))";
    // String branch2 = "(assert (> l h))";


    // // isSatisfiable2 assumes incremental mode; takes two params: constraint, and branch
    // // if branch = true, then ABC will save the current ID, clone it, give the clone a new ID,
    // //                   and continue from there in incremental mode
    // // if branch = false, then ABC will use the state associated with the current ID and
    // //                   continue from there in incremental mode; e.g., the current state is
    // //                   taken as the "initial" state for the next solve, and is modified from thereon
    // result = abcDriver.isSatisfiable2(branch1, true);
    // // since branch=true, we gotta get the ID if we want to come back to this state
    // String branch1_id = abcDriver.getCurrentID();


    // // lets get a random example, bounded, for h with bound of 5
    // Map<String, String> results = abcDriver.getSatisfyingExamplesRandomBounded(5);
    // for (Entry<String, String> var_result : results.entrySet()) {
    //   System.out.println(var_result.getKey() + " : \"" + var_result.getValue() + "\"");
    // }
    // System.out.println("----------DONE BRANCH1------------");


    // // lets go back and solve for branch 2 now
    // // load core id
    // abcDriver.loadID(core_constraint_id);
    // // tell ABC to branch and solve for branch2 constraint
    // result = abcDriver.isSatisfiable2(branch2, true);
    // // lets get a random example, bounded, for h with bound of 5
    // results = abcDriver.getSatisfyingExamplesRandomBounded(5);
    // for (Entry<String, String> var_result : results.entrySet()) {
    //   System.out.println(var_result.getKey() + " : \"" + var_result.getValue() + "\"");
    // }
    // System.out.println("-----------DONE BRANCH2-----------");


    // System.out.println("Before destroy");
    // String id_to_delete = abcDriver.getCurrentID();
    // abcDriver.destroyID(id_to_delete);
    // System.out.println("After destroy");



    // // lets go back to branch1
    // abcDriver.loadID(core_constraint_id);
    // // lets go incremental, but make branch=false; this will take branch1_id's state
    // // and continue on with it, without making a copy
    // String branch1_constraint2 = "(assert (= (charAt h 1) \"Z\"))";
    // result = abcDriver.isSatisfiable2(branch1_constraint2,false);

    // results = abcDriver.getSatisfyingExamplesRandomBounded(5);
    // for (Entry<String, String> var_result : results.entrySet()) {
    //   System.out.println(var_result.getKey() + " : \"" + var_result.getValue() + "\"");
    //   String mutated_model = abcDriver.mutateModel(var_result.getKey(),var_result.getValue());
    //   System.out.println(var_result.getKey() + "(mutated) : \"" + mutated_model + "\"");
    // }
    // System.out.println("-----------END-----------");
    
    
    // abcDriver.dispose(); // release resources
  }
}
