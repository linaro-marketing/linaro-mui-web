const path = require("path");

module.exports = {
  stories: ["../src/**/*.stories.mdx", "../src/**/*.stories.@(js|jsx|ts|tsx)"],
  addons: [
    "@storybook/addon-links",
    "@storybook/addon-essentials",
    "@storybook/preset-scss",
  ],
  core: {
    builder: "webpack5",
  },
  webpackFinal: async (config) => {
    config.resolve.modules = [path.resolve(__dirname, ".."), "node_modules"];
    config.resolve.alias = {
      ...config.resolve.alias,
      lib: path.resolve(__dirname, "../src/lib"),
      components: path.resolve(__dirname, "../src/components"),
    };
    return config;
  },
};
