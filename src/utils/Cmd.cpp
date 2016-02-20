/*
 * Cmd.cpp
 *
 *  Created on: Dec 15, 2015
 *      Author: baki
 */

#include "Cmd.h"

namespace Vlab {
namespace Util {
namespace Cmd {

std::string run_cmd(std::string cmd) {
  char buffer[256];
  int status;
  std::string result = "";
  FILE* pipe = popen(cmd.c_str(), "r");

  if (pipe == nullptr) {
    throw std::string("Not able to run command.");
  }

  while (fgets(buffer, 256, pipe) != nullptr) {
    result += buffer;
  }

  status = pclose(pipe);
  if (status == -1) {
    throw std::string("error while terminating command.");
  }

  std::string r_trimmed;
  std::stringstream ss (result);
  ss >> r_trimmed;
  return r_trimmed;
}

} /* namespace Cmd */
} /* namespace Util */
} /* namespace Vlab */
