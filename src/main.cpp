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

#include "Driver.h"

using namespace std;

int main(const int argc, const char **argv) {

	std::istream* in = &std::cin;
	std::ifstream* file = nullptr;
	std::string file_name;

	std::string project_root = "/home/baki/workspaces/default/ABC";

	bool model_count_only = false;
	std::string bound_string = "50";
	for (int i = 1; i < argc; ++i) {
		if (argv[i] == std::string ("-c")) {
			model_count_only = true;
		} else if (argv[i] == std::string ("-b")) {
			bound_string = argv[i+1];
			i++;
		} else if (argv[i] == std::string ("-f")) {

		} else {
			file_name = argv[i];
			file = new std::ifstream(file_name);
			in = file;
		}
	}

	int bound = std::stoi(bound_string);

	Vlab::Driver driver;
	driver.parse(in);
	driver.ast2dot("/home/baki/workspaces/default/ABC/test/parser_out.dot");

	return 0;
}
