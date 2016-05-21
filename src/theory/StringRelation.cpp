//
// Created by will on 3/6/16.
//

#include "StringRelation.h"

namespace Vlab {
namespace Theory {

StringRelation::StringRelation() :
      type(Type::NONE) {
  num_tracks = 0;
}

StringRelation::StringRelation(StringRelation::Type t, std::map<std::string, int> var_map, size_t ntracks) :
      type(t), var_track_map(var_map), num_tracks(ntracks) {
}

StringRelation::~StringRelation() {
}

StringRelation::StringRelation(const StringRelation &other) :
      type(other.type), var_track_map(other.var_track_map), num_tracks(other.num_tracks) {
}

StringRelation_ptr StringRelation::clone() const {
  return new StringRelation(*this);
}

StringRelation_ptr StringRelation::combine(StringRelation_ptr other_relation) {
  StringRelation_ptr result_relation = nullptr;
  std::map<std::string,int> variables;
  variables.insert(this->var_track_map.begin(), this->var_track_map.end());
  variables.insert(other_relation->var_track_map.begin(), other_relation->var_track_map.end());
  result_relation = new StringRelation();
  result_relation->setVariableTrackMap(variables);
  return result_relation;
}

void StringRelation::setType(Type type) {
  this->type = type;
}

StringRelation::Type StringRelation::getType() const {
  return this->type;
}

int StringRelation::getVariableIndex(std::string name) const {
  auto iter = var_track_map.find(name);
  if(iter == var_track_map.end()) {
    return -1;
  }
  return iter->second;
}

void StringRelation::setNumTracks(size_t ntracks) {
  this->num_tracks = ntracks;
}

size_t StringRelation::getNumTracks() const {
  return this->var_track_map.size();
}

std::map<std::string, int> StringRelation::getVariableTrackMap() {
  return this->var_track_map;
};

void StringRelation::setVariableTrackMap(std::map<std::string, int> vars) {
  this->var_track_map = std::map<std::string,int>(vars);
}

} /* namespace Theory */
} /* namespace Vlab */