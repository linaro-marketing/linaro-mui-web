// Generated with util/create-component.js

export type TMenuItem = {
  title: string;
  pathname?: string;
  subMenus?: TMenuItem[];
};

export interface DropdownMenuItemProps {
  menuItem: TMenuItem;
  menuShowingDropdown: string;
  setMenuShowingDropdown: (menuTitle: string) => void;
}
