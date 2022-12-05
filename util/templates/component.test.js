module.exports = (componentName) => ({
  content: `
  import React from "react";
  import { render } from "@testing-library/react";
  import ${componentName} from "./${componentName}";
  import { ${componentName}Props } from "./${componentName}.types";
  describe("${componentName} Test", () => {
    test("renders the Navbar component", () => {
      render(<${componentName} />);
    });
  });
  
  `,
  extension: `.test.tsx`,
});
