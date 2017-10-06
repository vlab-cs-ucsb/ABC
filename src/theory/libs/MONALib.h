/*
 * MONALib.h
 *
 *  Created on: Oct 5, 2017
 *      Author: baki
 */

#ifndef SRC_THEORY_LIBS_MONALIB_H_
#define SRC_THEORY_LIBS_MONALIB_H_

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <iostream>
#include <iterator>
#include <map>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include <glog/logging.h>
#include <mona/bdd.h>
#include <mona/bdd_external.h>
#include <mona/dfa.h>
#include <mona/mem.h>

namespace Vlab
{
  namespace Theory
  {
    namespace Libs
    {

      class MONALib
      {
         public:
          MONALib();
          virtual ~MONALib();
      };

    } /* namespace Libs */
  } /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_LIBS_MONALIB_H_ */
