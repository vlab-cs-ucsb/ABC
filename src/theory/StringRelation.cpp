//
// Created by will on 3/6/16.
//

#include "StringRelation.h"

namespace Vlab {
namespace Theory {

const int StringRelation::VLOG_LEVEL = 25;

StringRelation::StringRelation() :
      type(Type::NONE) {
  value = nullptr;
  num_tracks = 0;
}

StringRelation::StringRelation(Type t,std::map<std::string, int> *var_map,std::vector<Subrelation> subrels,
                    size_t ntracks, MultiTrackAutomaton_ptr value_auto) :
      type(t), var_track_map(var_map), subrelations(subrels), num_tracks(ntracks), value(value_auto) {
}

StringRelation::~StringRelation() {
}

StringRelation::StringRelation(const StringRelation &other) :
      type(other.type), var_track_map(other.var_track_map),
      subrelations(other.subrelations), num_tracks(other.num_tracks),
      value(other.value) {
}

StringRelation_ptr StringRelation::clone() const {
  return new StringRelation(*this);
}

StringRelation_ptr StringRelation::combine(StringRelation_ptr other_relation) {
  if(var_track_map != other_relation->get_variable_track_map()) {
    LOG(ERROR) << "error in stringrelation combine: track maps are not identical";
    return nullptr;
  }

  MultiTrackAutomaton_ptr result_auto = nullptr;
  StringRelation_ptr result_relation = nullptr;

  // combine their relations
  std::vector<Subrelation> subrels(this->subrelations);
  subrels.insert(subrels.end(), other_relation->subrelations.begin(), other_relation->subrelations.end());
  // intersect multitracks
  result_auto = this->value->intersect(other_relation->value);
  result_relation = new StringRelation(StringRelation::Type::INTERSECT,
                                       this->var_track_map,
                                       subrels,
                                       this->num_tracks,
                                       result_auto);
  return result_relation;
}

StringAutomaton_ptr StringRelation::get_variable_value_auto(std::string name) {
  StringAutomaton_ptr res;
  if(this->value == nullptr || var_track_map->find(name) == var_track_map->end()) {
    return nullptr;
  }
  DVLOG(VLOG_LEVEL) << "A1";
  DVLOG(VLOG_LEVEL) << "name: " << name << ", index: " << (*var_track_map)[name];
  res = value->getKTrack((*var_track_map)[name]);
  DVLOG(VLOG_LEVEL) << "A2";
  return res;
}

bool StringRelation::set_variable_value_auto(StringAutomaton_ptr value_auto, std::string name) {
  if(var_track_map->find(name) == var_track_map->end() || value == nullptr) {
    return false;
  }
  MultiTrackAutomaton_ptr temp_auto = new MultiTrackAutomaton(value_auto->getDFA(),(*var_track_map)[name],num_tracks);
  MultiTrackAutomaton_ptr result_auto = value->intersect(temp_auto);
  delete temp_auto;
  delete value;
  value = result_auto;
  return true;
}

void StringRelation::add_subrelation(StringRelation::Subrelation subrel) {
  this->subrelations.push_back(subrel);
}

std::vector<StringRelation::Subrelation> StringRelation::get_subrelation_list() {
  return subrelations;
}

MultiTrackAutomaton_ptr StringRelation::get_value_auto() {
  return value;
}

bool StringRelation::set_value_auto(MultiTrackAutomaton_ptr value_auto) {
  if(value_auto->getNumTracks() != get_num_tracks()) {
    return false;
  }
  value = value_auto;
  return true;
}

bool StringRelation::update_value_auto(MultiTrackAutomaton_ptr value_auto) {
  if(value == nullptr) {
    return set_value_auto(value_auto);
  }

  if(value_auto->getNumTracks() != value->getNumTracks()) {
    LOG(ERROR) << "in update_value_auto, track size does not match";
    return false;
  }
  MultiTrackAutomaton_ptr result_auto = value->intersect(value_auto);
  delete value;
  value = result_auto;
  return true;
}

void StringRelation::set_type(Type type) {
  this->type = type;
}

StringRelation::Type StringRelation::get_type() const {
  return this->type;
}

int StringRelation::get_variable_index(std::string name) const {
  auto iter = var_track_map->find(name);
  if(iter == var_track_map->end()) {
    return -1;
  }
  return iter->second;
}

void StringRelation::set_num_tracks(size_t ntracks) {
  this->num_tracks = ntracks;
}

size_t StringRelation::get_num_tracks() const {
  return this->var_track_map->size();
}

std::map<std::string, int>* StringRelation::get_variable_track_map() {
  return this->var_track_map;
};

void StringRelation::set_variable_track_map(std::map<std::string, int>* track_map) {
  this->var_track_map = track_map;
}

} /* namespace Theory */
} /* namespace Vlab */