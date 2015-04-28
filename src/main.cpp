/*
 ============================================================================
 Name        : main.cpp
 Author      : baki
 Version     :
 Copyright   : Copyright text goes here
 Description : Hello World in C++,
 ============================================================================
 */

#include <iostream>
#include <string>
#include <cstdlib>

//#define NDEBUG

#include <glog/logging.h>
#include "Driver.h"

using namespace std;

static const std::string get_default_output_dir();
static const std::string get_default_log_dir();

int main(const int argc, const char **argv) {

	std::istream* in = &std::cin;
	std::ifstream* file = nullptr;
	std::string file_name;

	std::string output_root = get_default_output_dir();
	std::string log_root = get_default_log_dir();
	FLAGS_log_dir = log_root;
	FLAGS_v = 19;
	FLAGS_logtostderr = 1;

	bool model_count_only = false;
	std::string bound_string = "50";
	for (int i = 1; i < argc; ++i) {
		if (argv[i] == std::string ("-c")) {
			model_count_only = true;
		} else if (argv[i] == std::string ("-b")) {
			bound_string = argv[i+1];
			i++;
		} else if (argv[i] == std::string ("-f")) {
			file_name = argv[i+1];
			file = new std::ifstream(file_name);
			in = file;
			i++;
		} else if (argv[i] == std::string ("-v")) {
			FLAGS_v = std::stoi(argv[i+1]);
			i++;
		} else {

		}
	}

	google::InitGoogleLogging(argv[0]);

	/* log test start */
	DLOG(INFO) << "debug log start";
	LOG(INFO) << "production log";
	DVLOG(1) << "vlog log";

	if (VLOG_IS_ON(1)) {
		std::cout << "yaaay" << std::endl;
	}
	/* log test end */



	int bound = std::stoi(bound_string);

	Vlab::Driver driver;
	driver.parse(in);
	if (VLOG_IS_ON(21)) {
		driver.ast2dot(&std::cout);
	}
	driver.ast2dot( output_root + "/parser_out.dot");

	driver.initializeSolver();

	return 0;
}

static const std::string get_default_output_dir() {
	  const char* env;
	  env = getenv("ABC_OUTPUT_DIR");
	  if (env != NULL && env[0] != '\0') {
	    return std::string(env);
	  }
	  int r = std::system("mkdir -p ./output");
	  return "./output";
}

static const std::string get_default_log_dir() {
	  const char* env;
	  env = getenv("ABC_LOG_DIR");
	  if (env != NULL && env[0] != '\0') {
	    return std::string(env);
	  }
	  int r = std::system("mkdir -p ./log");
	  return "./log";
}

