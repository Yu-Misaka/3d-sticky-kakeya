"use strict";

(async () => {
  const status = document.getElementById("status");
  const search = document.getElementById("search");
  const list = document.getElementById("declarations");
  try {
    const response = await fetch("../../declarations.json");
    if (!response.ok) throw new Error("Source index unavailable");
    const records = await response.json();
    const indexed = new Map(records.map(record => [record.name, record]));
    function filter() {
      const query = search.value.toLocaleLowerCase();
      const matches = records.filter(record => record.name.toLocaleLowerCase().includes(query));
      list.replaceChildren(...matches.map(record => {
        const item = document.createElement("li");
        const link = document.createElement("a");
        link.href = record.url;
        link.textContent = record.name;
        item.append(link);
        return item;
      }));
      status.textContent = `${matches.length} of ${records.length} declarations`;
    }
    function followHash() {
      let name;
      try {
        name = decodeURIComponent(location.hash.replace(/^#doc\//, ""));
      } catch {
        status.textContent = "This declaration link is malformed. Use the source index below.";
        return;
      }
      if (!name) return;
      const record = indexed.get(name);
      if (record && location.hash.startsWith("#doc/")) {
        location.replace(record.url);
      } else {
        search.value = name;
        filter();
        status.textContent = "This declaration is not in the blueprint’s source index.";
      }
    }
    document.getElementById("filter-form").hidden = false;
    search.addEventListener("input", filter);
    window.addEventListener("hashchange", followHash);
    filter();
    followHash();
  } catch {
    status.textContent = "The search index could not be loaded. The source links below remain available.";
  }
})();
