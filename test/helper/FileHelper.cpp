/*
 * FileHelper.cpp
 *
 *  Created on: Oct 29, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "FileHelper.h"

namespace Vlab {
namespace Test {

std::string FileHelper::getASCIIContents(std::string path) {
  std::ifstream file(path);
  std::string content_str;

  file.seekg(0, std::ios::end);
  content_str.reserve(file.tellg());
  file.seekg(0, std::ios::beg);

  content_str.assign((std::istreambuf_iterator<char>(file)),
              std::istreambuf_iterator<char>());
  return content_str;
}

std::string FileHelper::getExpectation(std::string nspace, std::string cname, std::string expectation) {
  std::string path = Path::EXPECTATION_PATH + "/" + nspace + "/" + cname + "/" + expectation;
  return getASCIIContents(path);
}


} /* namespace Test */
} /* namespace Vlab */
