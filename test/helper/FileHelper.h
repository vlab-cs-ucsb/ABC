/*
 * FileHelper.h
 *
 *  Created on: Oct 29, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef HELPER_FILEHELPER_H_
#define HELPER_FILEHELPER_H_

#include <iostream>
#include <string>
#include <fstream>
#include <streambuf>

#include "Path.h"

namespace Vlab {
namespace Test {

class FileHelper {
public:

  static std::string getASCIIContents(std::string path);
  static std::string getExpectation(std::string nspace, std::string cname, std::string expectation);

};

} /* namespace Test */
} /* namespace Vlab */

#endif /* HELPER_FILEHELPER_H_ */
